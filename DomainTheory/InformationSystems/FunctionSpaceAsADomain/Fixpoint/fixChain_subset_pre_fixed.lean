/-ai
A fix chain whose tokens lie in the element of an approximable endomap f stays inside a pre-fixed point of f: every value of the chain is contained in the carrier of that pre-fixed point.

The argument is by induction on the length. A chain of length zero is empty. At a successor step the preceding value lies in the pre-fixed point, and the entailment step supplies a subset of the token set whose inputs are entailed by that value and whose output union entails the new value. Those tokens lie in the relation of f. The input union is consistent because it is entailed by the preceding consistent set, so f relates the input union to the output union. Monotonicity of the relation moves the input to the preceding value and the output first to the new value and then to each of its singletons. The pre-fixed-point inequality places each such token in the pre-fixed point.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)














namespace ApproximableMap




/-- A `w`-chain under tokens from `f` stays inside a pre-fixed point. -/
theorem fixChain_subset_pre_fixed (f : ApproximableMap A A) (x : A.Element)
    (hpre : f.toElement x ≤ x) {w : Finset (FunToken A A)}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier) {n : Nat} {u : Finset α}
    (h : FixChain A w n u) : ↑u ⊆ x.carrier := by
  induction n generalizing u with
  | zero =>
    intro b hb
    rw [h] at hb
    exact False.elim (Finset.notMem_empty b hb)
  | succ n ih =>
    obtain ⟨u0, hu0, hu0C, huC, hEnt⟩ := h
    have hu0_sub := ih hu0
    obtain ⟨_, s, hs, hIn, hOut⟩ := hEnt
    have hps : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
      rel_of_mem_approx A f hw (hs hq)
    have hin : funInputUnion A A s ∈ A.Con :=
      A.con_subset
        (proposition_2_3_ii A hu0C (entSet_inputUnion_of_ent A A hIn))
        (subset_funion_right _ _)
    have hrel : f.rel (funInputUnion A A s) (funOutputUnion A A s) :=
      rel_input_output_union A A f s hps hin
    have hrel' : f.rel u0 (funOutputUnion A A s) :=
      f.mono hrel (entSet_inputUnion_of_ent A A hIn)
        (proposition_2_3_iii A (f.rel_cod hrel)) hu0C (f.rel_cod hrel)
    have hrel'' : f.rel u0 u :=
      f.mono hrel' (proposition_2_3_iii A hu0C) hOut hu0C huC
    intro b hb
    have hsing : f.rel u0 {b} :=
      f.mono hrel'' (proposition_2_3_iii A hu0C)
        (fun z hz => by
          rw [Finset.mem_singleton] at hz; subst hz
          exact A.ent_refl huC hb)
        hu0C (A.con_sing b)
    exact hpre ⟨u0, hu0_sub, hsing⟩

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
