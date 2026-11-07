module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.finJoinApprox
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.vshapeCounterexample
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.funPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
set_option linter.unusedVariables false
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive Counterexample712C

/-- Scott's Proposition 7.12: singleton/finJoin maps and the Vshape counterexample. -/
theorem proposition_712 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element),
      (PDfinJoinApproxMap₂ (V := V)).toElementMap₂ x y = V.PDfinJoin 2 ![x, y]) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (P : ComputablePresentation V)
      (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
      (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b),
      ComputableMap (prodPresentation P P) (V.PDPresentation P cons hconsp hcons)
        (finJoinMap_prod (V := V))) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X Y : Set α} (_hX : V.mem X) (_hY : V.mem Y)
      {W : Set (Set α)},
      (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
        (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element) {W : Set (Set α)},
      (V.PDfinJoin 2 ![x, y]).mem W ↔ (V.PDsingleton x).mem W ∧ (V.PDsingleton y).mem W) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element),
      V.PDfinJoin 2 ![x, y] = V.PDsingletonMeet (V.PDsingleton x) (V.PDsingleton y)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (P : ComputablePresentation V) {n k : ℕ},
      (PDsingletonApproxMap (V := V)).rel (P.X n) (V.Ypd P k) ↔
        ∃ b ∈ decodeList k, P.X n ⊆ P.X b) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x : V.Element),
      (PDsingletonApproxMap (V := V)).toElementMap x = V.PDsingleton x) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X X' : Set α} (hX : V.mem X) (hX' : V.mem X')
      (hX'X : X' ⊆ X),
      V.PDsingleton (V.principal hX) ≤ V.PDsingleton (V.principal hX')) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X : Set α} (hX : V.mem X),
      V.PDsingleton (V.principal hX) = V.PowerDomain.principal (V.PDmem_upSet hX)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (P : ComputablePresentation V)
      (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
      (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b),
      ComputableMap P (V.PDPresentation P cons hconsp hcons) (PDsingletonApproxMap (V := V))) ∧
    ¬ (Vshape ⊴ Vshape.PowerDomain) :=
  ⟨@PDfinJoinApproxMap₂_toElementMap, ⟨@PDfinJoinApproxMap₂_isComputable,
    ⟨@PDfinJoinApproxMap₂_rel_iff, ⟨@PDfinJoin_inter_two, ⟨@PDfinJoin_pair,
      ⟨@PDsingletonApproxMap_rel_Ypd_iff, ⟨@PDsingletonApproxMap_toElementMap,
        ⟨@PDsingleton_mono, ⟨@PDsingleton_principal, ⟨@singleton_isComputable,
          vshape_not_trianglelefteq_powerDomain⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
