import SmusniPositive.Syntax

/-! A full syntax/environment encoding. The alphabet contains no Code, context,
world, interpretation function, or semantic observation. -/
namespace SmusniPositive.Coding
universe u
variable {sig : Signature.{u}}

abbrev Alphabet (sig : Signature.{u}) := Nat ⊕ sig.Ground ⊕ sig.Name ⊕ sig.Key ⊕ sig.Predicate

inductive Tree (sig : Signature.{u}) : Type u where
  | nil : Tree sig
  | leaf : Alphabet sig → Tree sig
  | pair : Tree sig → Tree sig → Tree sig

def num (n : Nat) : Tree sig := .leaf (.inl n)
def ground (g : sig.Ground) : Tree sig := .leaf (.inr (.inl g))
def name (n : sig.Name) : Tree sig := .leaf (.inr (.inr (.inl n)))
def key (k : sig.Key) : Tree sig := .leaf (.inr (.inr (.inr (.inl k))))
def predicate (p : sig.Predicate) : Tree sig := .leaf (.inr (.inr (.inr (.inr p))))

def listTree : List (Tree sig) → Tree sig | [] => .nil | x :: xs => .pair x (listTree xs)
def vecTree {n : Nat} (f : Fin n → Tree sig) : Tree sig := listTree (List.ofFn f)

theorem listTree_injective {xs ys : List (Tree sig)} (h : listTree xs = listTree ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [listTree]
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      have eq := Tree.pair.inj h
      rw [eq.1, ih eq.2]

theorem vecTree_injective {n : Nat} {f g : Fin n → Tree sig} (h : vecTree f = vecTree g) : f = g := by
  have eq := listTree_injective h
  funext i
  have entries := congrArg (fun xs => xs[i.val]?) eq
  have same : some (f i) = some (g i) := by simpa [List.getElem?_ofFn, i.isLt] using entries
  exact Option.some.inj same

def groundTermTree : GroundTerm sig.Ground m → Tree sig
  | .var x => .pair (num 0) (num x.val)
  | .literal g => .pair (num 1) (ground g)

theorem groundTermTree_injective {a b : GroundTerm sig.Ground m}
    (h : groundTermTree a = groundTermTree b) : a = b := by
  cases a <;> cases b <;> simp [groundTermTree, num, ground] at h
  · exact congrArg GroundTerm.var (Fin.ext h)
  · exact congrArg GroundTerm.literal h

def termTree : Term sig m n → Tree sig
  | .top => num 0
  | .bot => num 1
  | .atom a args => .pair (num 2) (.pair (predicate a) (vecTree (fun i => groundTermTree (args i))))
  | .neg t => .pair (num 3) (termTree t)
  | .holdsVar x => .pair (num 4) (num x.val)
  | .holdsReify t => .pair (num 5) (termTree t)
  | .ctx k args body => .pair (num 6) (.pair (key k) (.pair (vecTree (fun i => groundTermTree (args i))) (termTree body)))
  | .read n body => .pair (num 7) (.pair (name n) (termTree body))
  | .allG body => .pair (num 8) (termTree body)
  | .allP body => .pair (num 9) (termTree body)

theorem groundArgs_injective {n : Nat} {a b : Fin n → GroundTerm sig.Ground m}
    (h : vecTree (fun i => groundTermTree (a i)) = vecTree (fun i => groundTermTree (b i))) : a = b := by
  have eq := vecTree_injective h
  funext i
  exact groundTermTree_injective (congrFun eq i)

theorem termTree_injective {m n} (a : Term sig m n) : ∀ b, termTree a = termTree b → a = b := by
  induction a with
  | top => intro b h; cases b <;> simp_all [termTree, num]
  | bot => intro b h; cases b <;> simp_all [termTree, num]
  | atom a args =>
    intro b h; cases b <;> simp [termTree, num, predicate] at h
    rcases h with ⟨rfl, h⟩
    exact congrArg (Term.atom a) (groundArgs_injective h)
  | neg a ih =>
    intro b h; cases b <;> simp [termTree, num] at h
    exact congrArg Term.neg (ih _ h)
  | holdsVar x =>
    intro b h; cases b <;> simp [termTree, num] at h
    exact congrArg Term.holdsVar (Fin.ext h)
  | holdsReify a ih =>
    intro b h; cases b <;> simp [termTree, num] at h
    exact congrArg Term.holdsReify (ih _ h)
  | ctx k args body ih =>
    intro b h; cases b <;> simp [termTree, num, key] at h
    rcases h with ⟨rfl, argsEq, bodyEq⟩
    have argsSame := groundArgs_injective argsEq
    have bodySame := ih _ bodyEq
    cases argsSame; cases bodySame; rfl
  | read n body ih =>
    intro b h; cases b <;> simp [termTree, num, name] at h
    rcases h with ⟨rfl, bodyEq⟩
    exact congrArg (Term.read n) (ih _ bodyEq)
  | allG body ih =>
    intro b h; cases b <;> simp [termTree, num] at h
    exact congrArg Term.allG (ih _ h)
  | allP body ih =>
    intro b h; cases b <;> simp [termTree, num] at h
    exact congrArg Term.allP (ih _ h)

/-- Closure scope sizes, term, and every entry of both finite environments survive. -/
def codeTree : Code sig → Tree sig
  | @Code.mk _ m n term g r =>
    .pair (num 20) (.pair (num m) (.pair (num n)
      (.pair (termTree term) (.pair (vecTree (fun i => ground (g i))) (vecTree (fun i => codeTree (r i)))))))

theorem codeTree_mk {m n} (term : Term sig m n) (g : Fin m → sig.Ground) (r : Fin n → Code sig) :
    codeTree (.mk term g r) = .pair (num 20) (.pair (num m) (.pair (num n)
      (.pair (termTree term) (.pair (vecTree (fun i => ground (g i))) (vecTree (fun i => codeTree (r i))))))) := rfl

theorem codeTree_injective (c : Code sig) : ∀ d, codeTree c = codeTree d → c = d := by
  induction c with
  | @mk m n term g r ih =>
    intro d eq
    cases d with
    | @mk m' n' term' g' r' =>
      simp only [codeTree_mk, Tree.pair.injEq, num, Tree.leaf.injEq, Sum.inl.injEq, true_and] at eq
      rcases eq with ⟨rfl, rfl, termEq, groundEq, propEq⟩
      have terms := termTree_injective _ _ termEq
      have gs := vecTree_injective groundEq
      have grounds : g = g' := by
        funext i
        have h := congrFun gs i
        simpa only [ground, Tree.leaf.injEq, Sum.inr.injEq, Sum.inl.injEq] using h
      have ps := vecTree_injective propEq
      have props : r = r' := funext (fun i => ih i _ (congrFun ps i))
      cases terms; cases grounds; cases props; rfl

/-- Reverse-Polish binary-tree coding reserves natural tags 0 and 1. Natural
payloads shift by two, so all symbols stay in the approved five-sort alphabet. -/
def treeWords : Tree sig → List (Alphabet sig)
  | .nil => [.inl 1]
  | .leaf (.inl n) => [.inl (n+2)]
  | .leaf (.inr a) => [.inr a]
  | .pair left right => treeWords left ++ treeWords right ++ [.inl 0]

def decodeStep (stack : Option (List (Tree sig))) : Alphabet sig → Option (List (Tree sig))
  | .inl 0 => match stack with
    | some (right :: left :: rest) => some (.pair left right :: rest)
    | _ => none
  | .inl 1 => stack.map (fun rest => .nil :: rest)
  | .inl (n+2) => stack.map (fun rest => .leaf (.inl n) :: rest)
  | .inr a => stack.map (fun rest => .leaf (.inr a) :: rest)

theorem treeWords_stack (t : Tree sig) (stack : List (Tree sig)) :
    (treeWords t).foldl decodeStep (some stack) = some (t :: stack) := by
  induction t generalizing stack with
  | nil => rfl
  | leaf a => cases a <;> rfl
  | pair left right ihl ihr =>
    simp only [treeWords, List.foldl_append, ihl, ihr, List.foldl_cons, List.foldl_nil, decodeStep]

def decodeTree (words : List (Alphabet sig)) : Option (Tree sig) :=
  match words.foldl decodeStep (some []) with | some [t] => some t | _ => none

theorem treeWords_roundtrip (t : Tree sig) : decodeTree (treeWords t) = some t := by
  simp only [decodeTree, treeWords_stack]

theorem treeWords_injective {a b : Tree sig} (h : treeWords a = treeWords b) : a = b := by
  have decoded := congrArg decodeTree h
  simp only [treeWords_roundtrip, Option.some.injEq] at decoded
  exact decoded

def encode (c : Code sig) : List (Alphabet sig) := treeWords (codeTree c)

theorem encode_injective {c d : Code sig} (h : encode c = encode d) : c = d :=
  codeTree_injective c d (treeWords_injective h)
end SmusniPositive.Coding
