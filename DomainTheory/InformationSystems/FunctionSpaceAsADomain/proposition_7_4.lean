module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.con_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
import DomainTheory.InformationSystems.InformationSystems.EntSet
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_fixed
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_le_of_pre_fixed
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_unique

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem closure_empty_eq_bot :
    A.closure (∅ : Finset α) A.con_empty = A.botElement := by
  apply le_antisymm
  · intro a ha
    exact A.ent_trans (A.con_sing A.bot) A.con_empty (EntSet.empty A _) ha
  · intro a ha
    exact A.ent_trans A.con_empty (A.con_sing A.bot)
      (fun x hx => by
        have : x = A.bot := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_bot A.con_empty)
      ha

theorem idMap_botElement : (idMap A).toElement A.botElement = A.botElement :=
  idMap.toElement A A.botElement

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
        (EntSet.union_mem A hu0C (entSet_inputUnion_of_ent A A hIn))
        (funion.subset_right _ _)
    have hrel : f.rel (funInputUnion A A s) (funOutputUnion A A s) :=
      rel_input_output_union A A f s hps hin
    have hrel' : f.rel u0 (funOutputUnion A A s) :=
      f.mono hrel (entSet_inputUnion_of_ent A A hIn)
        (EntSet.refl A (f.rel_cod hrel)) hu0C (f.rel_cod hrel)
    have hrel'' : f.rel u0 u :=
      f.mono hrel' (EntSet.refl A hu0C) hOut hu0C huC
    have huf : A.closure u huC ≤ f.toElement (A.closure u0 hu0C) := by
      intro a ha
      have hsub : ↑u ⊆ (f.toElement (A.closure u0 hu0C)).carrier := by
        intro b hb
        have hsing : f.rel u0 {b} :=
          f.mono hrel'' (EntSet.refl A hu0C)
            (fun z hz => by
              rw [Finset.mem_singleton] at hz; subst hz
              exact A.ent_refl huC hb)
            hu0C (A.con_sing b)
        refine ⟨u0, fun z hz => closure.subset A hu0C hz, hsing⟩
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
      fixElement_fixed B g
    calc
      h.toElement (A.closure u huC) ≤ h.toElement (f.toElement (A.closure u0 hu0C)) := hhuf
      _ = g.toElement (h.toElement (A.closure u0 hu0C)) := hcomm'
      _ ≤ g.toElement (fixElement B g) := hgle
      _ = fixElement B g := hfixg

theorem toElement_comp_fix_le (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    g.toElement (h.toElement (fixElement A f)) ≤ h.toElement (fixElement A f) := by
  have h1 : g.toElement (h.toElement (fixElement A f)) =
      h.toElement (f.toElement (fixElement A f)) := by
    rw [← comp.toElement, ← hcomm, comp.toElement]
  rw [h1, fixElement_fixed A f]

theorem fixElement_le_toElement_fix (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    fixElement B g ≤ h.toElement (fixElement A f) :=
  fixElement_le_of_pre_fixed B g (h.toElement (fixElement A f))
    (toElement_comp_fix_le A B f g h hcomm)

theorem toElement_fix_le_fixElement (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) ≤ fixElement B g := by
  intro Z ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨_, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  obtain ⟨n, hn⟩ := hv0
  have hcl := fixChain_toElement_le_fix A B f g h hcomm hstrict hw hn
  have hv0C := fixChain_con A hn
  have hrel' : h.rel v0 {Z} :=
    h.mono hrel hEnt (EntSet.refl B (h.rel_cod hrel)) hv0C (h.rel_cod hrel)
  have hZ : Z ∈ (h.toElement (A.closure v0 hv0C)).carrier :=
    ⟨v0, closure.subset A hv0C, hrel'⟩
  exact hcl hZ

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

namespace proposition_7_4

theorem ii (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f :=
  fixElement_fixed A f

theorem unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

theorem iii (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) = fixElement B g := by
  apply le_antisymm
  · exact toElement_fix_le_fixElement A B f g h hcomm hstrict
  · exact fixElement_le_toElement_fix A B f g h hcomm

end proposition_7_4

theorem proposition_7_4 :
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A),
      f.toElement (fixElement A f) = fixElement A f) ∧
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
      (A : InfoSys α) (B : InfoSys β)
      (f : ApproximableMap A A) (g : ApproximableMap B B) (h : ApproximableMap A B),
      comp h f = comp g h →
        h.toElement A.botElement = B.botElement →
          h.toElement (fixElement A f) = fixElement B g) ∧
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A) (φ : A.Element),
      f.toElement φ = φ →
        (∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) →
          φ = fixElement A f) :=
  ⟨@proposition_7_4.ii, @proposition_7_4.iii, @proposition_7_4.unique⟩

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
