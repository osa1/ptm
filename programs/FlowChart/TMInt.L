-- Turing machine interpreter in flow chart language (aka. L)
-- (mostly) as defined in Figure 4.4.
--
-- Differences from Figure 4.4:
-- * In if-then-else sytax we use keyword "then" instead of "goto".
-- * We use "halt()" instead of "return(expr)".
-- * We use "eq(e1, e2)" instead of "e1 == e2".
-- * We use "panic(expr)" instead of that awful return-syntax-error thing.

-- TODO: Figure out how is Instruction encoded.

read (Q, Right);

init:
  Qtail := Q;
  Left  := '();

loop:
  if eq(Qtail, '()) then stop else cont;

cont:
  Instruction   := first_instruction(Qtail);
  Qtail         := rest(QTail);
  Operator      := hd(tl(Instruction));

  if eq(Operator, 'right)  then do_right   else cont1;

cont1:
  if eq(Operator, 'left)   then do_left    else cond3;

cont2:
  if eq(Operator, 'write)  then do_write   else cont3;

cont3:
  if eq(Operator, 'goto)   then do_goto    else cont4;

cont4:
  if eq(Operator, 'if)     then do_if      else error;

do_right:
  Left      := cons(firstsym(Right), Left);
  Right     := tl(Right);
  goto loop;

do_left:
  Right     := cons(firstsym(Left), Right);
  Left      := tl(Left);
  goto loop;

do_write:
  Symbol    := hd(tl(tl(Instruction)));
  Right     := cons(Symbol, tl(Right));
  goto loop;

do_goto:
  Nextlabel := hd(tl(tl(Instruction)));
  Qtail     := new_tail(Nextlabel, Q);
  goto loop;

do_if:
  Symbol    := hd(tl(tl(Instruction)));
  Nextlabel := hd(tl(tl(tl(tl(Instruction)))));
  if eq(Symbol, firstsym(Right)) then jump else loop;

jump:
  Qtail := new_tail(Nextlabel, Q);
  goto loop;

error:
  -- different from Figure 4.4
  panic(Instruction);

stop:
  -- different from Figure 4.4
  halt();
