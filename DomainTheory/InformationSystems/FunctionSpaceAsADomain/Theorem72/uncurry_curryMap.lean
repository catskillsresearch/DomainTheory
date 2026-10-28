module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_self
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_comm_β
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_input_output_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_approxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.ProdCon_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.entSet_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_of_funTokens
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_curry_pointwise

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem uncurry_curryMap (h : ApproximableMap (productSystem A B) C) :
    uncurryMap A B C (curryMap A B C h) = h := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨m, ⟨hk, hsnd⟩, ⟨hCon, hw, hEnt⟩⟩

    obtain ⟨v, hfst, ⟨hv, hcurry⟩⟩ := hk
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEnt

    have hps : ∀ q ∈ t, h.rel (liftPair A B v q.val.1) q.val.2 :=
      fun q hq => hcurry q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B v (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h v hv t hps hin

    have hEntIn : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B (hsnd.1.2) hin
        (proposition_2_3_iv B (hsnd.1.2) hCon.2 hsnd.2.2
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)

    have hs : s ∈ (productSystem A B).Con := hfst.1
    have hEntv : A.EntSet (fstFinset A B s) v := hfst.2.2
    have hEntsnd : B.EntSet (sndFinset A B s) (sndFinset (functionSystem B C) B m) := hsnd.2.2
    have hEntIn' : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B hs.2 hin
        (proposition_2_3_iv B hs.2 hCon.2 hEntsnd (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)
    have hdom : liftPair A B (fstFinset A B s) (sndFinset A B s) ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hs.1 hs.2

    have hmid' : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s))
        (funOutputUnion B C t) :=
      h.mono hmid (entSet_liftPair A B hs.1 hs.2 hEntv hEntIn')
        (proposition_2_3_iii C (h.rel_cod hmid)) hdom (h.rel_cod hmid)

    have hEntLift : (productSystem A B).EntSet s (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
      intro p hp
      unfold liftPair at hp
      rcases mem_funion.mp hp with hp | hp
      · rcases (mem_liftLeft A B).1 hp with ⟨a, ha, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_refl hs.1 ha
        · intro _
          exact B.ent_bot hs.2
      · rcases (mem_liftRight A B).1 hp with ⟨b, hb, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_bot hs.1
        · intro _
          exact B.ent_refl hs.2 hb
    exact h.mono hmid' hEntLift hOut hs hw
  · intro hh
    have hs : s ∈ (productSystem A B).Con := h.rel_dom hh
    have hw : w ∈ C.Con := h.rel_cod hh
    let tok : FunToken B C := mkFunToken B C (sndFinset A B s) w hs.2 hw
    have hLiftCon : ProdCon A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) :=
      ProdCon_liftPair A B hs.1 hs.2
    have hEntLift : (productSystem A B).EntSet
        (liftPair A B (fstFinset A B s) (sndFinset A B s)) s := by
      intro p hp
      rcases p.property with hR | hL
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · rw [hR]; exact A.ent_bot hLiftCon.1
        · have hb : p.val.2 ∈ sndFinset A B s :=
            (mem_sndFinset A B).2 ⟨p, hp, hR, rfl⟩
          have hb' : p.val.2 ∈
              sndFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [sndFinset_liftPair]
            exact subset_funion_right _ _ hb
          exact B.ent_refl hLiftCon.2 hb'
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · have ha : p.val.1 ∈ fstFinset A B s :=
            (mem_fstFinset A B).2 ⟨p, hp, hL, rfl⟩
          have ha' : p.val.1 ∈
              fstFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [fstFinset_liftPair]
            exact subset_funion_left _ _ ha
          exact A.ent_refl hLiftCon.1 ha'
        · rw [hL]; exact B.ent_bot hLiftCon.2
    have hrel : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s)) w :=
      h.mono hh hEntLift (proposition_2_3_iii C hw) hLiftCon hw
    have hcurry_tok : (curryMap A B C h).rel (fstFinset A B s) {tok} := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have : p = tok := Finset.mem_singleton.mp hp
      subst this
      exact hrel
    let m := liftPair (functionSystem B C) B {tok} (sndFinset A B s)
    have hmCon : ProdCon (functionSystem B C) B m :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing tok) hs.2
    have hfst_m : fstFinset (functionSystem B C) B m =
        {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
      change fstFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [fstFinset.funion, fstFinset_liftLeft]
    have hsnd_m : sndFinset (functionSystem B C) B m =
        sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
          sndFinset A B s := by
      change sndFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [sndFinset.funion, sndFinset_liftRight]
    have hcurry_fst : (curryMap A B C h).rel (fstFinset A B s)
        (fstFinset (functionSystem B C) B m) := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have hp' : p ∈ {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
        rw [hfst_m] at hp
        exact hp
      rcases mem_funion.mp hp' with hp' | hp'
      · have : p = tok := Finset.mem_singleton.mp hp'
        subst this
        exact hrel
      · have hpbot : p = (functionSystem B C).bot :=
          Finset.mem_singleton.mp
            (fstFinset_liftRight (functionSystem B C) B (sndFinset A B s) hp')
        subst hpbot
        change h.rel (liftPair A B (fstFinset A B s) (funBot B C).val.1) (funBot B C).val.2
        simp only [funBot]
        exact h.mono h.empty_rel ((productSystem A B).entSet_empty _)
          (C.entSet_empty ∅) (ProdCon_liftPair A B hs.1 B.con_empty) C.con_empty
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    ·
      exact ⟨fstFinset A B s, ⟨hs, hs.1, proposition_2_3_iii A hs.1⟩, hcurry_fst⟩
    ·
      refine ⟨hs, hmCon.2, ?_⟩
      intro b hb
      have hb' : b ∈
          sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
            sndFinset A B s := by
        rwa [hsnd_m] at hb
      rcases mem_funion.mp hb' with hb' | hb'
      · have : b = B.bot := Finset.mem_singleton.mp
          (sndFinset_liftLeft (functionSystem B C) B {tok} hb')
        subst this
        exact B.ent_bot hs.2
      · exact B.ent_refl hs.2 hb'
    ·
      refine ⟨hmCon, hw, ?_⟩
      refine ⟨(curryMap A B C h).rel_cod hcurry_fst, {tok}, ?_, ?_, ?_⟩
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        have : tok ∈ fstFinset (functionSystem B C) B m := by
          rw [hfst_m]
          exact subset_funion_left _ _ (Finset.mem_singleton_self _)
        exact this
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        intro b hb
        have : b ∈ sndFinset (functionSystem B C) B m := by
          rw [hsnd_m]
          exact subset_funion_right _ _ hb
        exact B.ent_refl hmCon.2 this
      · rw [funOutputUnion.singleton]
        exact proposition_2_3_iii C hw

end InfoSys
end DomainTheory.InformationSystems
