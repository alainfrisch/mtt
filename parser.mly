%token TYPE EXPR
%token<string> UIDENT LIDENT TAG
%token EQUAL COMMA COLON ARROW SEMICOLON
%token EOF LBRACKET RBRACKET UNDERSCORE
%token<int> INT
%token LPAREN RPAREN LET LETN IN LEFT RIGHT IF THEN ELSE PIPE AMPERSAND DASH 
%token INFER RAND CHECK EVAL AND STAR PLUS AT

%nonassoc IN ELSE
%right AMPERSAND DASH
%right PIPE
%right COMMA
%nonassoc STAR PLUS LEFT RIGHT

%start prog
%type <Syntax.Phrase.t list> prog
%%

prog:
 | phrase prog { $1 :: $2 }
 | EOF { [] }

phrase:
 | TYPE UIDENT EQUAL typ { Syntax.Phrase.Type ($2,$4) }
 | EXPR UIDENT opt_args EQUAL expr { Syntax.Phrase.Expr ($2,$3,$5) } 
 | INFER expr IN typ { Syntax.Phrase.Infer ($2,$4) }
 | CHECK expr COLON typ ARROW typ { Syntax.Phrase.Check ($2,$4,$6) }
 | EVAL expr { Syntax.Phrase.Eval($2) }

opt_args:
 | LPAREN args RPAREN { $2 }
 | LPAREN RPAREN { [] }
 | { [] }

args:
 | LIDENT SEMICOLON args { $1::$3 }
 | LIDENT { [$1] }

typ:
 | LPAREN RPAREN { Syntax.Type.Eps }
 | UNDERSCORE LBRACKET typ_opt RBRACKET { Syntax.Type.AnyElt $3 }
 | LIDENT LBRACKET typ_opt RBRACKET { Syntax.Type.Elt ($1,$3) }
 | UIDENT { Syntax.Type.Ident $1 }
 | typ COMMA typ { Syntax.Type.Seq ($1,$3) }
 | typ AMPERSAND typ { Syntax.Type.And ($1,$3) }
 | typ PIPE typ { Syntax.Type.Alt ($1,$3) }
 | typ DASH typ { Syntax.Type.Diff ($1,$3) }
 | LPAREN typ RPAREN { $2 }
 | typ STAR { Syntax.Type.Star $1 }
 | typ PLUS { Syntax.Type.Plus $1 }

typ_opt:
 | typ { $1 }
 |     { Syntax.Type.Eps }


expr:
 | LIDENT { Syntax.Expr.Var $1 }
 | UIDENT expr_list_opt { Syntax.Expr.Call ($1,$2) }
 | LET bindings IN expr { Syntax.Expr.Let ($2,$4) }
 | LETN bindings IN expr { Syntax.Expr.LetN ($2,$4) }
 | LEFT expr { Syntax.Expr.Left $2 }
 | RIGHT expr { Syntax.Expr.Right $2 }
 | IF expr IN typ THEN expr ELSE expr { Syntax.Expr.Cond ($2,$4,$6,$8) }
 | LPAREN expr RPAREN { $2 }
 | LIDENT LBRACKET expr_opt RBRACKET expr_rest { Syntax.Expr.Elt ($1,$3,$5) }
 | UNDERSCORE LBRACKET expr_opt RBRACKET expr_rest { Syntax.Expr.CopyTag ($3,$5) }
 | RAND LPAREN typ RPAREN { Syntax.Expr.Random $3 }
 | LPAREN RPAREN { Syntax.Expr.Eps }
 | LPAREN expr SEMICOLON expr RPAREN { Syntax.Expr.Compose ($2,$4) }

expr_rest:
 | { Syntax.Expr.Eps }
 | COMMA expr { $2 }

bindings:
 | LIDENT EQUAL expr AND bindings { ($1,$3)::$5 }
 | LIDENT EQUAL expr { [($1,$3) ] }

expr_list_opt:
 | LPAREN expr_list RPAREN { $2 }
 | LPAREN RPAREN { [] }
 | { [] }

expr_list:
 | expr { [$1] }
 | expr SEMICOLON expr_list { $1::$3 }

expr_opt:
 | expr { $1 }
 |     { Syntax.Expr.Eps }
