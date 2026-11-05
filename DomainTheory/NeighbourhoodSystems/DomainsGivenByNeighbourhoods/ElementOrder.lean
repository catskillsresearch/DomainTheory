module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Approximation order on ideal elements: $x \le y$ means every neighbourhood of $x$
is a neighbourhood of $y$. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

/-- Two sequences of neighbourhoods are equivalent when each is refined by the other. -/
def SeqEquiv (X Y : ℕ → Set α) : Prop :=
  (∀ m, ∃ n, X n ⊆ Y m) ∧ (∀ n, ∃ m, Y m ⊆ X n)

/-- Neighbourhoods that eventually contain a term of the sequence $X$. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
