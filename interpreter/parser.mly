%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MULT LT
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ
%token RARROW FUN
%token REC

%token <int> INTV
%token <Syntax.id> ID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | LET x=ID EQ e=Expr SEMISEMI {Decl(x,e)}
  | LET REC f=ID EQ FUN n=ID RARROW e=Expr SEMISEMI {RecDecl(f,n,e)}

Expr :
    e=IfExpr { e }
  | e=LetExpr { e }
  | e=LetRecExpr { e }
  | e=LTExpr { e }
  | e=FunExpr { e }

LetExpr :
    LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }

LetRecExpr :
    LET REC f=ID EQ FUN n=ID RARROW e1=Expr IN e2=Expr {LetRecExp(f,n,e1,e2)}

LTExpr :
    l=PExpr LT r=PExpr { BinOp (Lt, l, r) }
  | e=PExpr { e }

PExpr :
    l=PExpr PLUS r=MExpr { BinOp (Plus, l, r) }
  | e=MExpr { e }

MExpr :
    e1=MExpr MULT e2=AppExpr { BinOp (Mult, e1, e2) }
  | e=AppExpr { e }

FunExpr :
    FUN x=ID RARROW e=Expr {FunExp(x, e)}

AppExpr :
    e1=AppExpr e2=AExpr {AppExp(e1,e2)}
  | e=AExpr{ e }

AExpr :
    i=INTV { ILit i }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var i }
  | LPAREN e=Expr RPAREN { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }
