%token TYPE EXPR
%token<string> UIDENT LIDENT
%token EQUAL COMMA COLON ARROW
%token EOF
%token<int> INT
%token LPAREN RPAREN LET IN LEFT RIGHT IF THEN ELSE PIPE AMPERSAND DASH INFER RAND CHECK

%right PIPE DASH
%right AMPERSAND

%start prog
%type <Syntax.Phrase.t list> prog
%%

prog:
 | phrase prog { $1 :: $2 }
 | EOF { [] }

phrase:
 | TYPE UIDENT EQUAL typ { Syntax.Phrase.Type ($2,$4) }
 | EXPR UIDENT EQUAL expr { Syntax.Phrase.Expr ($2,$4) }
 | INFER expr IN typ { Syntax.Phrase.Infer ($2,$4) }
 | CHECK expr COLON typ ARROW typ { Syntax.Phrase.Check ($2,$4,$6) }

typ:
 | INT { Syntax.Type.Int $1 }
 | LPAREN typ COMMA typ RPAREN { Syntax.Type.Pair ($2,$4) }
 | UIDENT { Syntax.Type.Ident $1 }
 | typ AMPERSAND typ { Syntax.Type.And ($1,$3) }
 | typ PIPE typ { Syntax.Type.Or ($1,$3) }
 | typ DASH typ { Syntax.Type.Diff ($1,$3) }
 | LPAREN typ RPAREN { $2 }

expr:
 | UIDENT { Syntax.Expr.Ident $1 }
 | LIDENT { Syntax.Expr.Var $1 }
 | LET LIDENT EQUAL expr IN expr { Syntax.Expr.Let ($2,$4,$6) }
 | INT { Syntax.Expr.Int $1 }
 | LEFT expr { Syntax.Expr.Left $2 }
 | RIGHT expr { Syntax.Expr.Right $2 }
 | IF expr IN typ THEN expr ELSE expr { Syntax.Expr.Cond ($2,$4,$6,$8) }
 | LPAREN expr RPAREN { $2 }
 | LPAREN expr COMMA expr RPAREN { Syntax.Expr.Pair ($2,$4) }
 | RAND LPAREN typ RPAREN { Syntax.Expr.Random $3 }

