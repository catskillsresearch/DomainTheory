module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powerUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Exercise 7.20: union map on the powerdomain is computable. -/
theorem example_720 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
      (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
      (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b),
      ComputableMap
        (V.PowerDomain.PDPresentation (V.PDPresentation P consV hconsVp hconsVs)
          (fun _ => 1) (Nat.Primrec.const 1)
          (fun a b => ⟨fun _ => ⟨0, ypd_zero_subset_inter P a b⟩, fun _ => rfl⟩))
        (V.PDPresentation P consV hconsVp hconsVs) (unionMap V)) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
      (Q : ComputablePresentation V.PowerDomain) (hQ : ∀ c, Q.X c = V.Ypd P c) {n m : ℕ},
      (unionMap V).rel (V.PowerDomain.Ypd Q n) (V.Ypd P m) ↔
        ∀ c ∈ decodeList n, ∀ a ∈ decodeList c, ∃ b ∈ decodeList m, P.X a ⊆ P.X b) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {LS : List (List (Set α))} {LY : List (Set α)}
      (hLS : ∀ l ∈ LS, ∀ X ∈ l, V.mem X) (hLY : ∀ Y ∈ LY, V.mem Y),
      (unionMap V).rel (⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X))
        (⋃ Y ∈ LY, V.upSet Y) ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y) :=
  ⟨@unionMap_isComputable, ⟨@unionMap_rel_Ypd_iff, @unionMap_rel_fin⟩⟩
end
end DomainTheory.NeighbourhoodSystems

