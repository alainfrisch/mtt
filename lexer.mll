{
  open Parser
}

let blank = [' ' '\009' '\012' '\010' '\013' ]
let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255' '_']
let uppercase = ['A'-'Z' '\192'-'\214' '\216'-'\222']
let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']


rule token = parse
  | blank+  { token lexbuf }
  | lowercase identchar* {
      match Lexing.lexeme lexbuf with
	| "let" -> LET
	| "in" -> IN
	| "if" -> IF
	| "then" -> THEN
	| "else" -> ELSE
	| "type" -> TYPE
	| "expr" -> EXPR
	| "infer" -> INFER
	| "rand" -> RAND
	| "check" -> CHECK
	| "eval" -> EVAL
	| s -> LIDENT s
    }
  | uppercase identchar* { UIDENT (Lexing.lexeme lexbuf) }
  | '`' identchar* { TAG (Lexing.lexeme lexbuf) }
  | "=" { EQUAL }
  | "," { COMMA }
  | ['0'-'9']+ { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "<" { LEFT }
  | ">" { RIGHT }
  | "|" { PIPE }
  | "&" { AMPERSAND }
  | ":" { COLON }
  | "->" { ARROW }
  | "(*" { comment 0 lexbuf }
  | eof { EOF }

and comment depth = parse
  | "*)" { if (depth = 0) then token lexbuf else comment (pred depth) lexbuf }
  | "(*" { comment (succ depth) lexbuf }
  | eof  { failwith "Unterminated comment" }
  | _    { comment depth lexbuf }
