module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.papplyEval

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Exercise 7.21: pointwise application/eval on powerdomains. -/
theorem example_721 :
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
      (Q : ComputablePresentation W)
      (heval : REPred (fun s => (eval V W).rel (Pf.X s.unpair.1)
        (P.X s.unpair.2.unpair.1) (Q.X s.unpair.2.unpair.2))),
      REPred (fun w => (papplyEval V W).rel ((funSpace V W).Ypd Pf w.unpair.1)
        (V.Ypd P w.unpair.2.unpair.1) (W.Ypd Q w.unpair.2.unpair.2))) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
      (Q : ComputablePresentation W) {Φc Ac Bc : ℕ},
      (papplyEval V W).rel ((funSpace V W).Ypd Pf Φc) (V.Ypd P Ac) (W.Ypd Q Bc) ↔
        ∀ g ∈ decodeList Φc, ∀ x ∈ decodeList Ac, ∃ y ∈ decodeList Bc,
          (eval V W).rel (Pf.X g) (P.X x) (Q.X y)) ∧
    (∀ {α β : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
      {X₀ : Set α} {Y₀ : Set β} (hX₀ : V.mem X₀) (hY₀ : W.mem Y₀),
      (papplyEval V W).rel ((funSpace V W).upSet (step X₀ Y₀)) (V.upSet X₀) (W.upSet Y₀)) :=
  ⟨@papplyEval_isComputable, ⟨@papplyEval_rel_Ypd_iff, @papplyEval_step_witness⟩⟩
end
end DomainTheory.NeighbourhoodSystems
