%token TYPE EXPR
%token<string> UIDENT LIDENT TAG
%token EQUAL COMMA COLON ARROW SEMICOLON
%token EOF LBRACKET RBRACKET UNDERSCORE
%token<int> INT
%token LPAREN RPAREN LET LETN IN LEFT RIGHT IF THEN ELSE PIPE AMPERSAND DASH INFER RAND CHECK EVAL

%right PIPE DASH
%right AMPERSAND
%nonassoc COMMA

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
 | EVAL expr expr { Syntax.Phrase.Eval($2,$3) }

typ:
 | LPAREN RPAREN { Syntax.Type.Eps }
 | UNDERSCORE LBRACKET typ_opt RBRACKET typ_rest { Syntax.Type.AnyElt ($3,$5) }
 | LIDENT LBRACKET typ_opt RBRACKET typ_rest { Syntax.Type.Elt ($1,$3,$5) }
 | UIDENT { Syntax.Type.Ident $1 }
 | typ AMPERSAND typ { Syntax.Type.And ($1,$3) }
 | typ PIPE typ { Syntax.Type.Or ($1,$3) }
 | typ DASH typ { Syntax.Type.Diff ($1,$3) }
 | LPAREN typ RPAREN { $2 }

typ_opt:
 | typ { $1 }
 |     { Syntax.Type.Eps }

typ_rest:
 | COMMA typ { $2 }
 |           { Syntax.Type.Eps }

expr:
 | LIDENT { Syntax.Expr.Var $1 }
 | UIDENT { Syntax.Expr.Ident $1 }
 | LET LIDENT EQUAL expr IN expr { Syntax.Expr.Let ($2,$4,$6) }
 | LETN LIDENT EQUAL expr IN expr { Syntax.Expr.LetN ($2,$4,$6) }
 | LEFT expr { Syntax.Expr.Left $2 }
 | RIGHT expr { Syntax.Expr.Right $2 }
 | IF expr IN typ THEN expr ELSE expr { Syntax.Expr.Cond ($2,$4,$6,$8) }
 | LPAREN expr RPAREN { $2 }
 | LIDENT LBRACKET expr_opt RBRACKET expr_rest { Syntax.Expr.Elt ($1,$3,$5) }
 | UNDERSCORE LBRACKET expr_opt RBRACKET expr_rest { Syntax.Expr.CopyTag ($3,$5) }
 | RAND LPAREN typ RPAREN { Syntax.Expr.Random $3 }
 | LPAREN RPAREN { Syntax.Expr.Eps }
 | LPAREN expr SEMICOLON expr RPAREN { Syntax.Expr.Compose ($2,$4) }

expr_opt:
 | expr { $1 }
 |     { Syntax.Expr.Eps }

expr_rest:
 | COMMA expr { $2 }
 |           { Syntax.Expr.Eps }
