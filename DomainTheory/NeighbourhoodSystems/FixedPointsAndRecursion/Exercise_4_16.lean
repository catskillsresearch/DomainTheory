module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_15

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_13

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace NeighborhoodSystem

def optimalFix (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
    (hfix : ∀ s ∈ S, f s = s) : V.Element :=
  monoFix f (f_sInf_le f hf S hS hfix)

theorem optimalFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    f (optimalFix f hf S hS hfix) = optimalFix f hf S hS hfix :=
  monoFix_isFixed f hf _

theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

theorem optimalFix_consistent (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub :=
  ⟨s, optimalFix_le f hf S hS hfix hs, le_refl s⟩

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

theorem example_416 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∀ (S : Set V.Element) (hS : S.Nonempty),
        (∀ s ∈ S, f s = s) → f (V.sInf S hS) ≤ V.sInf S hS) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element)
      (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
      (hfix : ∀ s ∈ S, f s = s) {s : V.Element},
      s ∈ S → ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element)
      (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
      (hfix : ∀ s ∈ S, f s = s) {s : V.Element},
      s ∈ S → optimalFix f hf S hS hfix ≤ s) :=
  ⟨@f_sInf_le, @optimalFix_consistent, @optimalFix_le⟩
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end
