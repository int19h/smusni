namespace SmusniPilot

inductive Bracket where
  | paren
  | brace
  | square
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Atom where
  | symbol (value : String)
  | string (value : String)
  deriving Repr, DecidableEq, BEq, Inhabited

inductive SExpr where
  | atom (value : Atom)
  | list (bracket : Bracket) (items : List SExpr)
  deriving Repr, BEq, Inhabited

namespace SExpr

def opening : Bracket → Char
  | .paren => '('
  | .brace => '{'
  | .square => '['

def closing : Bracket → Char
  | .paren => ')'
  | .brace => '}'
  | .square => ']'

def bracketOfOpen? : Char → Option Bracket
  | '(' => some .paren
  | '{' => some .brace
  | '[' => some .square
  | _ => none

def isWhitespace (character : Char) : Bool :=
  character == ' ' || character == '\n' || character == '\r' ||
    character == '\t'

def isDelimiter (character : Char) : Bool :=
  isWhitespace character || "(){}[];\"".contains character

def dropComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropComment rest

partial def skipSpace : List Char → List Char
  | [] => []
  | ';' :: rest => skipSpace (dropComment rest)
  | character :: rest =>
      if isWhitespace character then skipSpace rest else character :: rest

def readSymbol (characters : List Char) : String × List Char :=
  let rec loop (remaining : List Char) (reversed : List Char) :=
    match remaining with
    | [] => (String.ofList reversed.reverse, [])
    | character :: rest =>
        if isDelimiter character then
          (String.ofList reversed.reverse, remaining)
        else loop rest (character :: reversed)
  loop characters []

def readQuoted (characters : List Char) : Except String (String × List Char) :=
  let rec loop (remaining : List Char) (reversed : List Char) :=
    match remaining with
    | [] => .error "unterminated quoted string"
    | '"' :: rest => .ok (String.ofList reversed.reverse, rest)
    | '\\' :: 'n' :: rest => loop rest ('\n' :: reversed)
    | '\\' :: 'r' :: rest => loop rest ('\r' :: reversed)
    | '\\' :: 't' :: rest => loop rest ('\t' :: reversed)
    | '\\' :: '"' :: rest => loop rest ('"' :: reversed)
    | '\\' :: '\\' :: rest => loop rest ('\\' :: reversed)
    | '\\' :: escaped :: rest => loop rest (escaped :: reversed)
    | character :: rest => loop rest (character :: reversed)
  loop characters []

mutual
  partial def parseOne : List Char → Except String (SExpr × List Char)
    | characters =>
        match skipSpace characters with
        | [] => .error "expected s-expression, found end of input"
        | '"' :: rest => do
            let (value, remaining) ← readQuoted rest
            pure (.atom (.string value), remaining)
        | character :: rest =>
            match bracketOfOpen? character with
            | some bracket => do
                let (items, remaining) ← parseMany bracket rest
                pure (.list bracket items, remaining)
            | none =>
                if ")}]".contains character then
                  .error s!"unexpected closing delimiter {character}"
                else
                  let (value, remaining) := readSymbol (character :: rest)
                  if value.isEmpty then .error "empty symbol"
                  else .ok (.atom (.symbol value), remaining)

  partial def parseMany (bracket : Bracket) :
      List Char → Except String (List SExpr × List Char)
    | characters =>
        match skipSpace characters with
        | [] => .error s!"unterminated list, expected {closing bracket}"
        | character :: rest =>
            if character == closing bracket then .ok ([], rest)
            else if ")}]".contains character then
              .error s!"mismatched closing delimiter {character}"
            else do
              let (head, afterHead) ← parseOne (character :: rest)
              let (tail, afterTail) ← parseMany bracket afterHead
              pure (head :: tail, afterTail)
end

def parse (source : String) : Except String SExpr := do
  let (value, remaining) ← parseOne source.toList
  match skipSpace remaining with
  | [] => pure value
  | trailing =>
      .error s!"trailing data after s-expression: {String.ofList (trailing.take 80)}"

def escapeString (value : String) : String :=
  value.toList.foldl (fun result character =>
    result ++ match character with
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | '"' => "\\\""
      | '\\' => "\\\\"
      | other => String.singleton other) ""

partial def render : SExpr → String
  | .atom (.symbol value) => value
  | .atom (.string value) => "\"" ++ escapeString value ++ "\""
  | .list bracket items =>
      String.singleton (opening bracket) ++
        String.intercalate " " (items.map render) ++
        String.singleton (closing bracket)

def headSymbol? : SExpr → Option String
  | .list _ (.atom (.symbol head) :: _) => some head
  | _ => none

def fields : SExpr → List SExpr
  | .list _ (_ :: tail) => tail
  | _ => []

end SExpr

end SmusniPilot
