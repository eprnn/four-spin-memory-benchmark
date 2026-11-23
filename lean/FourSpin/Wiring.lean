import Std

/-! The three named partitions each supply one of two physical unordered edges.
The enumeration and site-relabeling proofs use kernel reduction on finite types. -/
namespace FourSpin.Wiring

inductive Site where | one | two | three | four
  deriving DecidableEq, BEq, Repr

inductive Axis where | a | b | c
  deriving DecidableEq, Repr

structure Choice where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

abbrev Edge := Site × Site

def sites : List Site := [.one, .two, .three, .four]
def axes : List Axis := [.a, .b, .c]

def edge (w : Choice) : Axis → Edge
  | .a => if w.a then (.three, .four) else (.one, .two)
  | .b => if w.b then (.two, .four) else (.one, .three)
  | .c => if w.c then (.two, .three) else (.one, .four)

def sameEdge (e f : Edge) : Bool :=
  (e == f) || (e.1 == f.2 && e.2 == f.1)

def incident (s : Site) (e : Edge) : Bool := (s == e.1) || (s == e.2)

def isStar (w : Choice) : Bool :=
  sites.any fun s => axes.all fun axis => incident s (edge w axis)

/-- Exactly three distinct edges missing a site of the four-site array. -/
def isTriangle (w : Choice) : Bool :=
  !(sameEdge (edge w .a) (edge w .b)) &&
  !(sameEdge (edge w .a) (edge w .c)) &&
  !(sameEdge (edge w .b) (edge w .c)) &&
  sites.any (fun s => axes.all fun axis => !(incident s (edge w axis)))

def choices : List Choice :=
  [false, true].flatMap fun a =>
    [false, true].flatMap fun b =>
      [false, true].map fun c => ⟨a, b, c⟩

theorem choices_exhaustive (w : Choice) : w ∈ choices := by
  obtain ⟨a, b, c⟩ := w
  cases a <;> cases b <;> cases c <;>
    repeat first | exact List.Mem.head _ | apply List.Mem.tail

theorem star_iff_not_triangle (w : Choice) : isStar w = !(isTriangle w) := by
  obtain ⟨a, b, c⟩ := w
  cases a <;> cases b <;> cases c <;> decide

theorem wiring_counts :
    choices.Nodup ∧ choices.length = 8 ∧
    (choices.filter isStar).length = 4 ∧ (choices.filter isTriangle).length = 4 := by
  decide

def starRep : Choice := ⟨false, false, false⟩    -- 12, 13, 14
def triangleRep : Choice := ⟨false, false, true⟩ -- 12, 13, 23

/-- The four permutations in the Klein four-group fix each named partition. -/
def relabel : Site → Site → Site
  | .one, s => s
  | .two, .one => .two     | .two, .two => .one
  | .two, .three => .four   | .two, .four => .three
  | .three, .one => .three  | .three, .two => .four
  | .three, .three => .one  | .three, .four => .two
  | .four, .one => .four    | .four, .two => .three
  | .four, .three => .two   | .four, .four => .one

theorem relabel_involutive (k s : Site) : relabel k (relabel k s) = s := by
  cases k <;> cases s <;> rfl

def relabelEdge (k : Site) (e : Edge) : Edge := (relabel k e.1, relabel k e.2)
def representative (w : Choice) := if isStar w then starRep else triangleRep

/-- The first two chosen edges intersect at a unique site. Move it to site one. -/
def relabeling (w : Choice) : Site :=
  match w.a, w.b with
  | false, false => .one  | false, true => .two
  | true, false => .three | true, true => .four

/-- A single involution carries all three physical edges onto the representative
at the original setting labels, without any permutation of the axes. -/
theorem relabel_to_representative (w : Choice) (axis : Axis) :
    sameEdge (relabelEdge (relabeling w) (edge w axis))
      (edge (representative w) axis) = true := by
  obtain ⟨a, b, c⟩ := w
  cases a <;> cases b <;> cases c <;> cases axis <;> decide

structure Bits where
  one : Bool
  two : Bool
  three : Bool
  four : Bool
  deriving DecidableEq, Repr

def bit (s : Bits) : Site → Bool
  | .one => s.one | .two => s.two | .three => s.three | .four => s.four

def transpose (e : Edge) (site : Site) : Site :=
  if site == e.1 then e.2 else if site == e.2 then e.1 else site

/-- Permute the four physical bit coordinates of a computational basis state. -/
def swapBits (e : Edge) (s : Bits) : Bits :=
  ⟨bit s (transpose e .one), bit s (transpose e .two),
   bit s (transpose e .three), bit s (transpose e .four)⟩

theorem swap_coordinates (e : Edge) (s : Bits) (site : Site) :
    bit (swapBits e s) site = bit s (transpose e site) := by
  cases site <;> rfl

theorem six_physical_swaps (a b c d : Bool) :
    let s : Bits := ⟨a, b, c, d⟩
    swapBits (.one, .two) s = ⟨b, a, c, d⟩ ∧
    swapBits (.three, .four) s = ⟨a, b, d, c⟩ ∧
    swapBits (.one, .three) s = ⟨c, b, a, d⟩ ∧
    swapBits (.two, .four) s = ⟨a, d, c, b⟩ ∧
    swapBits (.one, .four) s = ⟨d, b, c, a⟩ ∧
    swapBits (.two, .three) s = ⟨a, c, b, d⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem physical_swap_involutive (w : Choice) (axis : Axis) (s : Bits) :
    swapBits (edge w axis) (swapBits (edge w axis) s) = s := by
  obtain ⟨a, b, c⟩ := w
  cases a <;> cases b <;> cases c <;> cases axis <;> rfl

def relabelBits (k : Site) (s : Bits) : Bits :=
  ⟨bit s (relabel k .one), bit s (relabel k .two),
   bit s (relabel k .three), bit s (relabel k .four)⟩

/-- Relabeling the four registers intertwines their actual bit swaps for
every setting of the wiring, with one common relabeling across settings. -/
theorem relabel_swap_to_representative (w : Choice) (axis : Axis) (s : Bits) :
    relabelBits (relabeling w) (swapBits (edge w axis) s) =
    swapBits (edge (representative w) axis) (relabelBits (relabeling w) s) := by
  obtain ⟨a, b, c⟩ := w
  cases a <;> cases b <;> cases c <;> cases axis <;> rfl

#print axioms choices_exhaustive
#print axioms star_iff_not_triangle
#print axioms wiring_counts
#print axioms relabel_involutive
#print axioms relabel_to_representative
#print axioms swap_coordinates
#print axioms six_physical_swaps
#print axioms physical_swap_involutive
#print axioms relabel_swap_to_representative

end FourSpin.Wiring
