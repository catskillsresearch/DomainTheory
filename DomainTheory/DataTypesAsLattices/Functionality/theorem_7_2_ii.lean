
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.emptyE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.prodE
public import DomainTheory.DataTypesAsLattices.Functionality.sumE
public import DomainTheory.DataTypesAsLattices.Functionality.Ea
public import DomainTheory.DataTypesAsLattices.Functionality.kerE
public import DomainTheory.DataTypesAsLattices.Functionality.Nrel
public import DomainTheory.DataTypesAsLattices.Functionality.Nk
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.iterateE
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinRel
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinGood
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_ii_of_typed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.2 (ii).** Maps in `E_{a ∘→ b}` are graphs of
maps from `a` to `b`, corresponding to `E_a → E_b`. -/
theorem theorem_7_2_ii {a b : Pomega} (ha : Retract a) (hb : Retract b)
    (f g : Pomega) :
    (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
      ((arrowE (Ea a) (Ea b)).rel f g →
        (Ea (arrowR a b)).rel (funOf (arrowR a b) f) (funOf (arrowR a b) g)) ∧
      ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g) := by
  refine ⟨fun hf => theorem_7_2_ii_of_typed hf, ?_, ?_⟩
  · intro hfg
    rcases hfg with ⟨hfgraph, hggraph, hpres⟩
    have hftyped : typed (funOf (arrowR a b) f) (arrowR a b) :=
      (retract_app (arrowR.isRetract ha hb) f).symm
    have hgtyped : typed (funOf (arrowR a b) g) (arrowR a b) :=
      (retract_app (arrowR.isRetract ha hb) g).symm
    refine ⟨hftyped, hgtyped, ?_⟩
    rw [arrowR.app, arrowR.app]
    apply graph_ext
    intro x
    simp only [comp_app]
    have hax : typed (funOf a x) a := (retract_app ha x).symm
    have hsame := hpres (funOf a x) (funOf a x) ⟨hax, hax, rfl⟩
    have hfeq : funOf f (funOf a x) = funOf g (funOf a x) := hsame.2.2
    have hfb : typed (funOf f (funOf a x)) b := hsame.1
    have hgb : typed (funOf g (funOf a x)) b := hsame.2.1
    rw [← hfb, ← hgb, hfeq]
  · intro hfg
    rcases hfg with ⟨hf, hg, rfl⟩
    have hmem := theorem_7_2_ii_of_typed hf
    exact ⟨hmem.1, hmem.1, hmem.2.2⟩

end DomainTheory.DataTypesAsLattices
