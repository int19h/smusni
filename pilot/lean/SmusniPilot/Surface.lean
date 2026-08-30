import SmusniPilot.SExpr
import SmusniPilot.Inventory

namespace SmusniPilot

inductive SurfaceKind where
  | primitive (head : Primitive)
  | defined (head : SurfaceHead)
  | gap (head : GapHead)
  | tool (head : ToolHead)
  | lexical (head : String)
  | variable (name : String)
  | unknown (head : String)
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
  | .variable name => name
  | .unknown head => head

def classifySurfaceKind (head : String) : SurfaceKind :=
  if head.startsWith "$" then .variable head
  else let qualified := "term:" ++ head
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
              | none => .unknown head

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

def SurfaceTerm.isBinderDescriptor : SurfaceTerm → Bool
  | .form _ (.variable _) arguments =>
      arguments.any fun
        | .atom (.symbol "::") => true
        | _ => false
  | _ => false

partial def SurfaceTerm.definedHeadsWith (lexicalHeads : List String) :
    SurfaceTerm → List SurfaceHead
  | .atom (.string _) => []
  | .atom (.symbol raw) =>
      if raw.toNat?.isSome || raw.startsWith "$" || raw.startsWith ":" ||
          lexicalHeads.contains raw
      then []
      else match SurfaceHead.ofName ("term:" ++ raw) with
        | some head => [head]
        | none => []
  | .empty _ => []
  | .form _ (.defined head) arguments =>
      head :: arguments.flatMap (definedHeadsWith lexicalHeads)
  | term@(.form _ (.variable _) arguments) =>
      if term.isBinderDescriptor then []
      else arguments.flatMap (definedHeadsWith lexicalHeads)
  | .form _ _ arguments =>
      arguments.flatMap (definedHeadsWith lexicalHeads)
  | .application _ function arguments =>
      definedHeadsWith lexicalHeads function ++
        arguments.flatMap (definedHeadsWith lexicalHeads)

partial def SurfaceTerm.offendingHeadsWith (lexicalHeads : List String) :
    SurfaceTerm → List String
  | .atom (.string _) => []
  | .atom (.symbol raw) =>
      if raw.toNat?.isSome || raw.startsWith "$" || raw.startsWith ":" ||
          lexicalHeads.contains raw
      then []
      else
        let qualified := "term:" ++ raw
        if (Primitive.ofName qualified).isSome ||
            (SurfaceHead.ofName qualified).isSome then []
        else [qualified]
  | .empty _ => []
  | .form _ (.gap head) arguments =>
      head.name :: arguments.flatMap (offendingHeadsWith lexicalHeads)
  | .form _ (.tool head) arguments =>
      head.name :: arguments.flatMap (offendingHeadsWith lexicalHeads)
  | .form _ (.unknown head) arguments =>
      ("term:" ++ head) :: arguments.flatMap (offendingHeadsWith lexicalHeads)
  | term@(.form _ (.variable _) arguments) =>
      if term.isBinderDescriptor then []
      else arguments.flatMap (offendingHeadsWith lexicalHeads)
  | .form _ (.defined _) arguments =>
      arguments.flatMap (offendingHeadsWith lexicalHeads)
  | .form _ _ arguments => arguments.flatMap (offendingHeadsWith lexicalHeads)
  | .application _ function arguments =>
      offendingHeadsWith lexicalHeads function ++
        arguments.flatMap (offendingHeadsWith lexicalHeads)

partial def SurfaceTerm.structuralErrors : SurfaceTerm → List String
  | .atom (.symbol raw) =>
      if ["λ", "Bind", "Context", "Vague"].contains raw then
        ["term:" ++ raw ++ ":missing-form"]
      else []
  | .atom (.string _) | .empty _ => []
  | .form _ (.primitive .lambda) arguments =>
      (if arguments.length == 2 then [] else ["term:λ:bad-arity"]) ++
        arguments.flatMap structuralErrors
  | .form _ (.primitive .bind) arguments =>
      (if arguments.length >= 3 && arguments.length % 2 == 1 then []
       else ["term:Bind:bad-clauses"]) ++
        arguments.flatMap structuralErrors
  | .form _ (.primitive .vague) arguments =>
      (if arguments.length == 1 then [] else ["term:Vague:bad-arity"]) ++
        arguments.flatMap structuralErrors
  | .form _ _ arguments => arguments.flatMap structuralErrors
  | .application _ function arguments =>
      function.structuralErrors ++ arguments.flatMap structuralErrors

partial def SurfaceTerm.containsDollarVariable : SurfaceTerm → Bool
  | .atom (.symbol raw) => raw.startsWith "$"
  | .atom (.string _) | .empty _ => false
  | .form _ (.variable _) _ => true
  | .form _ _ arguments => arguments.any containsDollarVariable
  | .application _ function arguments =>
      function.containsDollarVariable || arguments.any containsDollarVariable

partial def SurfaceTerm.hasVariableUnderDefined : SurfaceTerm → Bool
  | .atom _ | .empty _ => false
  | .form _ (.defined _) arguments =>
      arguments.any containsDollarVariable ||
        arguments.any hasVariableUnderDefined
  | .form _ _ arguments => arguments.any hasVariableUnderDefined
  | .application _ function arguments =>
      function.hasVariableUnderDefined ||
        arguments.any hasVariableUnderDefined

def SurfaceTerm.argumentLabelErrors : List SurfaceTerm → List String
  | [] => []
  | [.atom (.symbol label)] =>
      if label.startsWith ":" then ["term:$label:missing-value"] else []
  | .atom (.symbol label) :: .atom (.symbol value) :: rest =>
      if label.startsWith ":" && value.startsWith ":" then
        ["term:$label:label-value"] ++ argumentLabelErrors rest
      else argumentLabelErrors (.atom (.symbol value) :: rest)
  | _ :: rest => argumentLabelErrors rest

partial def SurfaceTerm.labelErrors : SurfaceTerm → List String
  | .atom _ | .empty _ => []
  | .form _ _ arguments =>
      argumentLabelErrors arguments ++ arguments.flatMap labelErrors
  | .application _ function arguments =>
      argumentLabelErrors arguments ++ function.labelErrors ++
        arguments.flatMap labelErrors

end SmusniPilot
