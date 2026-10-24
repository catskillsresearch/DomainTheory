module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L492 EXERCISE 1.22 topology of a domain -/
/-- **Exercise 1.22.** Each basic neighbourhood `[X]` is open. -/
theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  ⟨fun _ hx => ⟨X, hx, subset_rfl⟩⟩

/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.OpenFilter U :=
  ⟨fun h => h, fun h => h⟩

/-- **Exercise 1.22, condition (i).** Every open set is upward closed under the approximation order
`⊑`: if `x ∈ 𝒰` and `x ⊑ y` then `y ∈ 𝒰`. (This is a *consequence* of (ii): the basic
neighbourhood `[X] ⊆ 𝒰` witnessing `x ∈ 𝒰` also contains every `y ⊒ x`.) -/
theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU.out x hxU
  exact hXU (hxy X hX)

/-- **Exercise 1.22 (characterization of open sets).** A subset `𝒰 ⊆ |𝒟|` is open iff
(i) it is upward closed under `⊑`, and (ii) every point of `𝒰` has a basic neighbourhood `[X]`
(`X ∈ x`) contained in `𝒰`. -/
theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU.out⟩
  · rintro ⟨_, h2⟩
    exact ⟨h2⟩

/-- **Exercise 1.22, condition (iii).** The approximation order is recovered from the topology:
`x ⊑ y` iff every open set containing `x` also contains `y`.

* `→` is upward closure of opens (`isOpen_isUpperSet`);
* `←` tests against the open basic neighbourhood `[X]` for each `X ∈ x`. -/
theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

/-- **Exercise 1.22 (assembled).** Open sets are upward closed; basic opens are open; opens are
exactly the upper sets covered by basic opens; and `⊑` is specialization in the Scott topology. -/
example :
    (∀ {U : Set V.Element}, IsOpen U → ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
      (∀ X : Set α, IsOpen (V.basicOpen X)) ∧
      (∀ U : Set V.Element,
        IsOpen U ↔
          (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
            (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U)) ∧
      (∀ x y : V.Element, x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U) :=
  ⟨V.isOpen_isUpperSet, V.isOpen_basicOpen, V.isOpen_iff_upper_basic, V.le_iff_isOpen_imp⟩

/-- The approximation order `⊑` is the opposite of Mathlib's specialization preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
