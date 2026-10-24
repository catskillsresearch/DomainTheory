module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_ii

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)


theorem fixChain_toElement_le_fix (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement)
    {w : Finset (FunToken A A)}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier) {n : Nat} {u : Finset α}
    (hchain : FixChain A w n u) :
    h.toElement (A.closure u (fixChain_con A hchain)) ≤ fixElement B g := by
  induction n generalizing u with
  | zero =>
    have hu : u = ∅ := hchain
    subst hu
    simpa [closure_empty_eq_bot A, hstrict] using
      (botElement.le B (fixElement B g))
  | succ n ih =>
    obtain ⟨u0, hu0, hu0C, huC, hEnt⟩ := hchain
    have ih' := ih hu0
    obtain ⟨_, s, hs, hIn, hOut⟩ := hEnt
    have hps : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq => by
      simpa [mem_approxMap_toElement] using hw (Finset.mem_coe.2 (hs hq))
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
    have huf : A.closure u huC ≤ f.toElement (A.closure u0 hu0C) := by
      intro a ha
      have hsub : ↑u ⊆ (f.toElement (A.closure u0 hu0C)).carrier := by
        intro b hb
        have hsing : f.rel u0 {b} :=
          f.mono hrel'' (proposition_2_3_iii A hu0C)
            (fun z hz => by
              rw [Finset.mem_singleton] at hz; subst hz
              exact A.ent_refl huC hb)
            hu0C (A.con_sing b)
        refine ⟨u0, fun z hz => A.subset_closure hu0C hz, hsing⟩
      exact (f.toElement (A.closure u0 hu0C)).closed u a hsub ha
    have hhuf : h.toElement (A.closure u huC) ≤
        h.toElement (f.toElement (A.closure u0 hu0C)) :=
      toElement_mono h huf
    have hcomm' : h.toElement (f.toElement (A.closure u0 hu0C)) =
        g.toElement (h.toElement (A.closure u0 hu0C)) := by
      rw [← comp.toElement, hcomm, comp.toElement]
    have hgle : g.toElement (h.toElement (A.closure u0 hu0C)) ≤
        g.toElement (fixElement B g) :=
      toElement_mono g ih'
    have hfixg : g.toElement (fixElement B g) = fixElement B g :=
      proposition_7_4_ii B g
    calc
      h.toElement (A.closure u huC) ≤ h.toElement (f.toElement (A.closure u0 hu0C)) := hhuf
      _ = g.toElement (h.toElement (A.closure u0 hu0C)) := hcomm'
      _ ≤ g.toElement (fixElement B g) := hgle
      _ = fixElement B g := hfixg

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
