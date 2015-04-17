{-# LANGUAGE DeriveFunctor, QuasiQuotes #-}

module CoreLike.Step where

import Control.Arrow (second)
import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Language.Haskell.Exts as HSE
import qualified Text.PrettyPrint.Leijen as PP

import CoreLike.Parser
import CoreLike.Syntax
import CoreLike.ToHSE

type Env = M.Map Var Term

data Restriction
  = Subst Var Term
  | NEq Var (Either DataCon Literal) -- TODO: Use this in default branches.
  deriving (Show)

data Step a
  = Transient a
  | Split [([Restriction], a)]
  | Stuck -- Reason
          -- TODO: we may want to do something different depending on whether
          -- we're stuck because the term is already a value or not
  deriving (Show, Functor)

-- TODO: Should we keep stepping subexpressions when a term is stuck because of
--       a type error?

-- TODO: There should be a combinator-based approach for splitting subterms and
--       then combining results.
--       Find a way to nested step cases.

step :: Env -> Term -> Step Term
step env (Var v) = maybe Stuck Transient $ M.lookup v env
step _   Value{} = Stuck

step _   (App (Value (Lambda arg body)) var) = Transient $ substTerm arg (Var var) body
step _   (App Value{} _) = Stuck
step env (App t v) =
    case step env t of
      Transient t' -> Transient $ App t' v
      Split ts     -> Split $ map (second $ flip App v) ts
      Stuck        -> Stuck -- TODO: can we do something about the argument here?

step env (PrimOp op args) =
    case stepArgs args of
      Transient args' -> Transient $ PrimOp op args'
      Split args'     -> Split $ map (second $ PrimOp op) args'
      Stuck           ->
        let vals = [ v | Value v <- args ]
         in if length vals == length args
              then stepPrimOp op vals
              else Stuck
  where
    stepArgs :: [Term] -> Step [Term]
    stepArgs [] = Stuck
    stepArgs (t : ts) =
      case step env t of
        Transient t' -> Transient $ t' : ts
        Split t'     -> Split $ map (second (: ts)) t'
        Stuck        ->
          case stepArgs ts of
            Transient ts' -> Transient $ t : ts'
            Split ts'     -> Split $ map (second (t :)) ts'
            Stuck         -> Stuck

step _   (Case d@(Value (Data con args)) cases) = findBranch cases
  where
    findBranch :: [(AltCon, Term)] -> Step Term
    findBranch []                                  = Stuck
                               -- TODO: Is this possible when cases are exhaustive?
                               --       (Maybe with GADTs?)
    findBranch ((DataAlt con' args' , rhs) : rest)
      | con == con' = Split [(zipWith (\v v' -> Subst v (Var v')) args args', rhs)]
      | otherwise   = findBranch rest
    findBranch ((LiteralAlt{}       , _  ) : rest) = findBranch rest
    findBranch ((DefaultAlt Nothing , rhs) : _   ) = Transient rhs
    findBranch ((DefaultAlt (Just v), rhs) : _   ) = Split [([Subst v d], rhs)]

step _   (Case d@(Value (Literal lit)) cases) = findBranch cases
  where
    findBranch :: [(AltCon, Term)] -> Step Term
    findBranch []                                  = Stuck
    findBranch ((DataAlt{}          , _  ) : rest) = findBranch rest
    findBranch ((LiteralAlt lit'    , rhs) : rest)
      | lit == lit' = Transient rhs
      | otherwise   = findBranch rest
    findBranch ((DefaultAlt Nothing , rhs) : _   ) = Transient rhs
    findBranch ((DefaultAlt (Just v), rhs) : _   ) = Split [([Subst v d], rhs)]

step _   (Case Value{} _) = Stuck
step env (Case scrt cases) =
    case step env scrt of
      Transient scrt' -> Transient $ Case scrt' cases
      Split scrts     -> Split $ map (second $ flip Case cases) scrts
      Stuck           ->
        case stepCases cases of
          Transient cases' -> Transient $ Case scrt cases'
          Split cases'     -> Split $ map (second $ Case scrt) cases'
          Stuck            -> Stuck
  where
    stepCases :: [(AltCon, Term)] -> Step [(AltCon, Term)]
    stepCases [] = Stuck
    -- TODO: Can we make any progress in case bodies here?
    stepCases ((pattern, rhs) : rest) =
      case step env rhs of
        Transient rhs' -> Transient ((pattern, rhs') : rest)
        Split rhs'     -> Split $ map (\(cs, rhs'') -> (cs, (pattern, rhs'') : rest)) rhs'
        Stuck          ->
          case stepCases rest of
            Transient rest' -> Transient ((pattern, rhs) : rest')
            Split rest'     -> Split $ map (second ((pattern, rhs) :)) rest'
            Stuck           -> Stuck

step env (LetRec binders body) =
    case iterBs env' binders of
      Transient binders' -> Transient (LetRec binders' body)
      Split binders'     -> Split $ map (second $ flip LetRec body) binders'
      Stuck              ->
        case step env' body of
          Transient body' -> Transient $ LetRec binders body'
          Split bs        -> Split $ map (second $ LetRec binders) bs
          Stuck           -> Stuck
  where
    env' = foldl' (\m (k, v) -> M.insert k v m) env binders

    iterBs :: Env -> [(Var, Term)] -> Step [(Var, Term)]
    iterBs _ [] = Stuck
    iterBs env ((v, t) : bs) =
      case step (M.insert v t env) t of
        Transient t' -> Transient ((v, t') : bs)
        Split ts     -> Split $ map (\(restrs, t') -> (restrs, (v, t') : bs)) ts
        Stuck        ->
          case iterBs env bs of
            Transient bs' -> Transient ((v, t) : bs')
            Split bss     -> Split $ map (\(restrs, bs') -> (restrs, (v, t) : bs')) bss
            Stuck         -> Stuck

-- TODO: Reduce boilerplate here
stepPrimOp :: PrimOp -> [Value] -> Step Term
stepPrimOp Add [Literal (Int i1), Literal (Int i2)] =
  Transient $ Value $ Literal $ Int $ i1 + i2
stepPrimOp Subtract [Literal (Int i1), Literal (Int i2)] =
  Transient $ Value $ Literal $ Int $ i1 - i2
stepPrimOp Multiply [Literal (Int i1), Literal (Int i2)] =
  Transient $ Value $ Literal $ Int $ i1 * i2
stepPrimOp Divide [Literal (Int i1), Literal (Int i2)] =
  Transient $ Value $ Literal $ Int $ i1 `div` i2
stepPrimOp _ _ = Stuck

------------
-- * Testing

-- Use haskell-src-exts quoter(haskell-src-exts-qq) once #10279 is fixed.

parseEnv :: [(String, String)] -> Env
parseEnv [] = M.empty
parseEnv ((v, t) : rest) =
    let t' = either (error . (++) "Can't parse term in env: ") id $ parseTerm t
     in M.insert v t' $ parseEnv rest

env1 = parseEnv
  [ ("even", "\\x -> case x of { 0 -> True; _ -> odd  (x - 1) }")
  , ("odd",  "\\x -> case x of { 1 -> True; _ -> even (x - 1) }")
  , ("simple", "even 1 || odd 2")
  ]

pprintEnv :: Env -> String
pprintEnv =
    ($ "") . PP.displayS . PP.renderPretty 1 100 . PP.list . map (uncurry ppBinding) . M.toList
  where
    ppBinding :: Var -> Term -> PP.Doc
    ppBinding v t =
      PP.text v PP.<+> PP.equals PP.<$> PP.indent 1 (PP.string (HSE.prettyPrint $ termToHSE t))
