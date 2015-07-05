-- Program listed in 4.4.2
-- (slightly modified to fix the syntax)

read (Name, Namelist, Valuelist);

search:
  if eq(Name, hd(Namelist)) then found else cont;

cont:
  Valuelist := tl(Valuelist);
  Namelist  := tl(Namelist);
  goto search;

found:
  Ret := hd(Valuelist);
  halt();
