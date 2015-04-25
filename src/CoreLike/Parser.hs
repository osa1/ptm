{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase, TupleSections #-}

module CoreLike.Parser where

import Control.Arrow (first)
import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Language.Haskell.Exts as HSE

import CoreLike.Syntax

data ParserState = ParserState
  { varSupply :: !Int }

freshVar :: Parser Var
freshVar = do
    s <- get
    let ret = "v" ++ show (varSupply s)
    put s{varSupply = varSupply s + 1}
    return ret

initParserState :: ParserState
initParserState = ParserState 0

newtype Parser a = Parser { unwrapParser :: StateT ParserState (Except String) a }
  deriving (Functor, Applicative, Monad, MonadState ParserState, MonadError String)

parse :: String -> Either String [(Var, Term)]
parse contents =
    case HSE.parseFileContents contents of
      HSE.ParseOk hse ->
         runExcept (evalStateT (unwrapParser $ transformHSE hse) initParserState)
      HSE.ParseFailed loc str ->
        Left $ "fromParseResult: Parse failed at [" ++ HSE.srcFilename loc
                 ++ "] (" ++ show (HSE.srcLine loc) ++ ":" ++ show (HSE.srcColumn loc) ++ "): " ++ str

parseFile :: FilePath -> IO (Either String [(Var, Term)])
parseFile file = parse <$> readFile file

prims :: M.Map HSE.QName PrimOp
prims = M.fromList $ map (first $ HSE.UnQual . HSE.Symbol) symbols
  where
    symbols =
      [ ("+", Add), ("-", Subtract), ("*", Multiply), ("/", Divide), ("%", Modulo),
        ("==", Equal), ("<", LessThan), ("<=", LessThanEqual) ]

parseTerm :: String -> Either String Term
parseTerm str =
    case HSE.parseExp str of
      HSE.ParseOk hse ->
         runExcept (evalStateT (unwrapParser $ transformExp hse) initParserState)
      HSE.ParseFailed loc err ->
        Left $ "fromParseResult: Parse failed at [" ++ HSE.srcFilename loc
                 ++ "] (" ++ show (HSE.srcLine loc) ++ ":" ++ show (HSE.srcColumn loc) ++ "): " ++ err

parseTerm' :: String -> Term
parseTerm' = either error id . parseTerm

transformHSE :: HSE.Module -> Parser [(Var, Term)]
transformHSE (HSE.Module _ _ _ _ _ _ decls) = mapM transformDecl decls

transformDecl :: HSE.Decl -> Parser (Var, Term)
transformDecl (HSE.FunBind [HSE.Match _loc fName pats _ rhs _]) = do
    args <- collectArgs pats
    rhs' <- transformRhs rhs
    return (nameVar fName, lambda args rhs')
transformDecl (HSE.PatBind _loc (HSE.PVar name) rhs _) = (nameVar name,) <$> transformRhs rhs

transformDecl (HSE.FunBind _) = throwError $ "Function groups are not supported."
transformDecl decl = throwError $ "Unsupported declaration: " ++ show decl

transformRhs :: HSE.Rhs -> Parser Term
transformRhs (HSE.GuardedRhss rhss) = throwError $ "Guarded RHSs are not supported: " ++ show rhss
transformRhs (HSE.UnGuardedRhs e) = transformExp e

transformExp :: HSE.Exp -> Parser Term
transformExp (HSE.Var qname) = Var <$> transformQName qname
transformExp (HSE.Con qname) = fmap Var $ transformQName qname >>= conFunctionName
transformExp (HSE.Lit lit) = Value <$> transformLit lit
transformExp (HSE.App e1 e2) = do
    e1' <- transformExp e1
    e2' <- transformExp e2
    introLet e2' $ \v -> return $ App e1' v
transformExp (HSE.InfixApp e1 op e2) = do
    e1' <- transformExp e1
    e2' <- transformExp e2
    op' <- opName op
    introLet e1' $ \v1 ->
      introLet e2' $ \v2 ->
        case op of
          HSE.QConOp{} ->
            -- FIXME: Make sure the application is not partial, in that case we
            -- should be using function variant instead
            return $ Value $ Data op' [v1, v2]
          HSE.QVarOp qname ->
            case M.lookup qname prims of
              Nothing -> return $ App (App (Var op') v1) v2
              -- FIXME: No need to alpha-convert for prims
              Just pOp -> return $ PrimOp pOp [Var v1, Var v2]
transformExp (HSE.Lambda _ pats body) = lambda <$> collectArgs pats <*> transformExp body
transformExp (HSE.If e1 e2 e3) = do
    e1' <- transformExp e1
    e2' <- transformExp e2
    e3' <- transformExp e3
    return $ Case e1' [(DataAlt "True" [], e2'), (DataAlt "False" [], e3')]
transformExp (HSE.Paren e) = transformExp e
transformExp (HSE.Case e alts) = Case <$> transformExp e <*> mapM transformAlt alts
transformExp (HSE.List es) = list =<< mapM transformExp es
transformExp (HSE.Let (HSE.BDecls decls) body) =
    LetRec <$> mapM transformDecl decls <*> transformExp body
transformExp e = throwError $ "Unsupported exp: " ++ show e

-- | Introduce a let-binding for the term. Combines 'LetRec's returned by term
-- builder.
introLet :: Term -> (Var -> Parser Term) -> Parser Term
introLet (Var v) f = f v
introLet t       f = do
    v <- freshVar
    f v >>= \case
      LetRec binds body -> return $ LetRec ((v, t) : binds) body
      t'                -> return $ LetRec [(v, t)] t'

elimBinds :: [(Var, Term)] -> Term -> Term
elimBinds [] t = t
elimBinds bs t = LetRec bs t

collectArgs :: [HSE.Pat] -> Parser [Var]
collectArgs [] = return []
collectArgs (HSE.PVar v : ps) = (nameVar v :) <$> collectArgs ps
collectArgs (p : _) = throwError $ "Unsupported pattern in function arguments: " ++ show p

transformAlt :: HSE.Alt -> Parser (AltCon, Term)
transformAlt (HSE.Alt _ pat rhs _) = (,) <$> transformPat pat <*> transformRhs rhs

transformPat :: HSE.Pat -> Parser AltCon
transformPat (HSE.PVar v) = return $ DefaultAlt (Just $ nameVar v)
transformPat (HSE.PApp qname pats) = do
    con <- transformQName qname
    args <- collectArgs pats
    return $ DataAlt con args
transformPat (HSE.PInfixApp p1 op p2) = do
    con <- transformQName op
    args <- collectArgs [p1, p2]
    return $ DataAlt con args
transformPat (HSE.PList []) = return $ DataAlt "[]" []
transformPat (HSE.PLit _sign lit) = transformLitPat lit
transformPat HSE.PWildCard = DefaultAlt . Just <$> freshVar
transformPat p = throwError $ "Unsupported pattern: " ++ show p

transformLitPat :: HSE.Literal -> Parser AltCon
transformLitPat (HSE.Int i) = return $ LiteralAlt (Int i)
transformLitPat l = throwError $ "Unsupported literal pattern: " ++ show l

-- | Return function name for the data constructor, if data constructor is
-- known, otherwise fail.
conFunctionName :: Var -> Parser Var
conFunctionName = return . id -- FIXME

transformLit :: HSE.Literal -> Parser Value
transformLit (HSE.Int i) = return $ Literal $ Int i
transformLit l = throwError $ "Unsupported literal expression: " ++ show l

lambda :: [Var] -> Term -> Term
lambda []       t = t
lambda (v : vs) t = Value $ Lambda v (lambda vs t)

list :: [Term] -> Parser Term
list [] = return $ Value $ Data "[]" []
list ts = do
    -- generate names for terms, if term is already a value, return itself in vars
    (lets, vars) <- termLets ts
    -- generate cons pairs as lets
    ((_, t) : conses) <- consLets vars
    return $ LetRec (lets ++ conses) t
  where
    termLets :: [Term] -> Parser ([(Var, Term)], [Var])
    termLets [] = return ([], [])
    termLets (t : rest) = do
      (lets, vars) <- termLets rest
      case t of
        Var v -> return (lets, v : vars)
        _     -> do
          v <- freshVar
          return $ ((v, t) : lets, v : vars)

    consLets :: [Var] -> Parser [(Var, Term)]
    consLets [] = return []
    consLets [v] = do
      cons <- freshVar
      return [(cons, Value $ Data "(:)" [v, nil])]
    consLets (v : vs) = do
      rest@((tv, _) : _) <- consLets vs
      cons <- freshVar
      return $ (cons, Value $ Data "(:)" [v, tv]) : rest

nil :: Var
nil = "nil"

nameVar :: HSE.Name -> Var
nameVar (HSE.Ident s)  = s
nameVar (HSE.Symbol s) = s

transformQName :: HSE.QName -> Parser Var
transformQName q@HSE.Qual{} = throwError $ "Qualified names are not supported: " ++ show q
transformQName (HSE.UnQual n) = return $ nameVar n
transformQName (HSE.Special HSE.Cons) = return "(:)"
transformQName (HSE.Special HSE.UnitCon) = return "()"
transformQName (HSE.Special s) = throwError $ "Unsupported special name: " ++ show s

opName :: HSE.QOp -> Parser Var
opName (HSE.QVarOp qName) = transformQName qName
opName (HSE.QConOp qName) =
    -- FIXME: should be careful about partial constructor applications
    transformQName qName
