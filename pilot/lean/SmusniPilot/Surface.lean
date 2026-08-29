import SmusniPilot.SExpr
import SmusniPilot.Inventory

namespace SmusniPilot

inductive SurfaceKind where
  | primitive (head : Primitive)
  | defined (head : SurfaceHead)
  | gap (head : GapHead)
  | tool (head : ToolHead)
  | lexical (head : String)
  deriving Repr, BEq, Inhabited

inductive SurfaceTerm where
  | atom (value : Atom)
  | form (bracket : Bracket) (kind : SurfaceKind)
      (arguments : List SurfaceTerm)
  | application (bracket : Bracket) (function : SurfaceTerm)
      (arguments : List SurfaceTerm)
  | empty (bracket : Bracket)
  deriving Repr, BEq, Inhabited

def rawTermName (qualified : String) : String :=
  (qualified.drop 5).toString

def SurfaceKind.spelling : SurfaceKind → String
  | .primitive head => rawTermName head.name
  | .defined head => rawTermName head.name
  | .gap head => rawTermName head.name
  | .tool head => rawTermName head.name
  | .lexical head => head

def classifySurfaceKind (head : String) : SurfaceKind :=
  let qualified := "term:" ++ head
  match Primitive.ofName qualified with
  | some primitive => .primitive primitive
  | none =>
      match SurfaceHead.ofName qualified with
      | some defined => .defined defined
      | none =>
          match GapHead.ofName qualified with
          | some gap => .gap gap
          | none =>
              match ToolHead.ofName qualified with
              | some tool => .tool tool
              | none => .lexical head

def SurfaceTerm.ofSExprWithLexicon (lexicalHeads : List String) :
    SExpr → SurfaceTerm
  | .atom value => .atom value
  | .list bracket [] => .empty bracket
  | .list bracket (.atom (.symbol head) :: arguments) =>
      let kind :=
        if lexicalHeads.contains head then .lexical head
        else classifySurfaceKind head
      .form bracket kind
        (arguments.map (ofSExprWithLexicon lexicalHeads))
  | .list bracket (function :: arguments) =>
      .application bracket (ofSExprWithLexicon lexicalHeads function)
        (arguments.map (ofSExprWithLexicon lexicalHeads))

def SurfaceTerm.ofSExpr : SExpr → SurfaceTerm :=
  ofSExprWithLexicon []

def SurfaceTerm.toSExpr : SurfaceTerm → SExpr
  | .atom value => .atom value
  | .empty bracket => .list bracket []
  | .form bracket kind arguments =>
      .list bracket
        (.atom (.symbol kind.spelling) :: arguments.map toSExpr)
  | .application bracket function arguments =>
      .list bracket (function.toSExpr :: arguments.map toSExpr)

def SurfaceTerm.definedHeads : SurfaceTerm → List SurfaceHead
  | .atom _ | .empty _ => []
  | .form _ (.defined head) arguments =>
      head :: arguments.flatMap definedHeads
  | .form _ _ arguments => arguments.flatMap definedHeads
  | .application _ function arguments =>
      function.definedHeads ++ arguments.flatMap definedHeads

def SurfaceTerm.offendingHeads : SurfaceTerm → List String
  | .atom _ | .empty _ => []
  | .form _ (.gap head) arguments =>
      head.name :: arguments.flatMap offendingHeads
  | .form _ (.tool head) arguments =>
      head.name :: arguments.flatMap offendingHeads
  | .form _ _ arguments => arguments.flatMap offendingHeads
  | .application _ function arguments =>
      function.offendingHeads ++ arguments.flatMap offendingHeads

end SmusniPilot
