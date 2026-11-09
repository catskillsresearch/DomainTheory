module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.pairMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
import DomainTheory.InformationSystems.InformationSystems.InfoSys.con_empty
import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem_more

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem rel_of_funTokens (h : ApproximableMap (productSystem A B) C)
    (u : Finset α) (hu : u ∈ A.Con) (t : Finset (FunToken B C))
    (hps : ∀ p ∈ t, h.rel (liftPair A B u p.val.1) p.val.2)
    (hin : funInputUnion B C t ∈ B.Con) :
    h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) := by
  induction t using Finset.induction_on with
  | empty =>
    rw [funInputUnion.empty, funOutputUnion.empty]
    have hdom : liftPair A B u ∅ ∈ (productSystem A B).Con :=
      ProdCon_liftPair A B hu B.con_empty
    exact h.mono h.empty_rel
      (EntSet.empty (productSystem A B) _)
      (EntSet.empty C ∅) hdom C.con_empty
  | insert p t' hpnot ih =>
    have hps' : ∀ q ∈ t', h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (Finset.mem_insert_of_mem hq)
    have hin' : funInputUnion B C t' ∈ B.Con :=
      B.con_subset hin (by
        rw [funInputUnion.insert]
        exact funion.subset_right _ _)
    have ih' := ih hps' hin'
    have hp : h.rel (liftPair A B u p.val.1) p.val.2 :=
      hps p (Finset.mem_insert_self p t')
    have hinU : p.val.1 ∪' funInputUnion B C t' ∈ B.Con := by
      rwa [funInputUnion.insert] at hin
    have hEnt_p : B.EntSet (p.val.1 ∪' funInputUnion B C t') p.val.1 :=
      fun y hy => B.ent_refl hinU (funion.subset_left _ _ hy)
    have hEnt_t : B.EntSet (p.val.1 ∪' funInputUnion B C t') (funInputUnion B C t') :=
      fun y hy => B.ent_refl hinU (funion.subset_right _ _ hy)
    have hdomU : liftPair A B u (p.val.1 ∪' funInputUnion B C t') ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hu hinU
    have h1 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t')) p.val.2 :=
      h.mono hp
        (entSet_liftPair A B hu hinU (EntSet.refl A hu) hEnt_p)
        (EntSet.refl C (h.rel_cod hp)) hdomU (h.rel_cod hp)
    have h2 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t'))
        (funOutputUnion B C t') :=
      h.mono ih'
        (entSet_liftPair A B hu hinU (EntSet.refl A hu) hEnt_t)
        (EntSet.refl C (h.rel_cod ih')) hdomU (h.rel_cod ih')
    rw [funInputUnion.insert, funOutputUnion.insert]
    exact h.union_right h1 h2

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem funCon_of_curry_pointwise (h : ApproximableMap (productSystem A B) C)
    {u : Finset α} (hu : u ∈ A.Con) {s : Finset (FunToken B C)}
    (hps : ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2) :
    FunCon B C s :=
  fun t ht hin =>
    h.rel_cod (rel_of_funTokens A B C h u hu t (fun p hp => hps p (ht hp)) hin)

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def curryMap (h : ApproximableMap (productSystem A B) C) :
    ApproximableMap A (functionSystem B C) where
  rel u s :=
    u ∈ A.Con ∧ ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2
  rel_dom hrel := hrel.1
  rel_cod hrel := funCon_of_curry_pointwise A B C h hrel.1 hrel.2
  empty_rel := ⟨A.con_empty, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩
  union_right := by
    rintro u s s' ⟨hu, hps⟩ ⟨_, hps'⟩
    refine ⟨hu, ?_⟩
    intro p hp
    rcases funion.mem.mp hp with hp | hp
    · exact hps p hp
    · exact hps' p hp
  mono := by
    rintro u u' s s' ⟨hu, hps⟩ hEntu hEnts hu' hs'
    refine ⟨hu', ?_⟩
    intro p hp

    have hEntp : FunEnt B C s p := hEnts p hp
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEntp
    have hps_t : ∀ q ∈ t, h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (EntSet.union_mem B p.property.1 (entSet_inputUnion_of_ent B C hIn))
        (funion.subset_right _ _)
    have hmid : h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h u hu t hps_t hin
    have hmid' : h.rel (liftPair A B u' p.val.1) (funOutputUnion B C t) :=
      h.mono hmid
        (entSet_liftPair A B hu' p.property.1 hEntu
          (entSet_inputUnion_of_ent B C hIn))
        (EntSet.refl C (h.rel_cod hmid))
        (ProdCon_liftPair A B hu' p.property.1) (h.rel_cod hmid)
    exact h.mono hmid'
      (EntSet.refl (productSystem A B) (ProdCon_liftPair A B hu' p.property.1))
      hOut (ProdCon_liftPair A B hu' p.property.1) p.property.2

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def applyMap : ApproximableMap (productSystem (functionSystem B C) B) C where
  rel s t :=
    ∃ (hs : ProdCon (functionSystem B C) B s) (ht : t ∈ C.Con),
      FunEnt B C (fstFinset (functionSystem B C) B s)
        (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht)
  rel_dom := fun ⟨hs, _, _⟩ => hs
  rel_cod := fun ⟨_, ht, _⟩ => ht
  empty_rel := by
    have hs : ProdCon (functionSystem B C) B ∅ :=
      ⟨by rw [fstFinset.empty]; exact (functionSystem B C).con_empty,
        by rw [sndFinset.empty]; exact B.con_empty⟩
    refine ⟨hs, C.con_empty, ?_⟩
    have hfst : fstFinset (functionSystem B C) B (∅ : Finset _) = ∅ := fstFinset.empty _ _
    have hsnd : sndFinset (functionSystem B C) B (∅ : Finset _) = ∅ := sndFinset.empty _ _
    simp only [hfst, hsnd]
    exact (functionSystem B C).ent_bot (functionSystem B C).con_empty
  union_right := by
    rintro s t t' ⟨hs, ht, hEntt⟩ ⟨_, ht', hEntt'⟩
    obtain ⟨hw, s1, hs1, hIn1, hOut1⟩ := hEntt
    obtain ⟨_, s2, hs2, hIn2, hOut2⟩ := hEntt'
    have hsub : s1 ∪' s2 ⊆ fstFinset (functionSystem B C) B s :=
      funion.subset_iff.mpr ⟨hs1, hs2⟩
    have hin : funInputUnion B C (s1 ∪' s2) ∈ B.Con := by
      rw [funInputUnion.funion]
      have hEntU : B.EntSet (sndFinset (functionSystem B C) B s)
          (funInputUnion B C s1 ∪' funInputUnion B C s2) :=
        EntSet.union B
          (entSet_inputUnion_of_ent B C hIn1)
          (entSet_inputUnion_of_ent B C hIn2)
      exact B.con_subset (EntSet.union_mem B hs.2 hEntU) (funion.subset_right _ _)
    have hout : funOutputUnion B C s1 ∪' funOutputUnion B C s2 ∈ C.Con := by
      have := hw _ hsub hin
      rwa [funOutputUnion.funion] at this
    have htt' : t ∪' t' ∈ C.Con := by
      have hEntt2 : C.EntSet (funOutputUnion B C s1 ∪' funOutputUnion B C s2) (t ∪' t') :=
        EntSet.union C
          (EntSet.mono C (C.con_subset hout (funion.subset_left _ _)) hout
            (funion.subset_left _ _) hOut1 (Finset.Subset.refl _))
          (EntSet.mono C (C.con_subset hout (funion.subset_right _ _)) hout
            (funion.subset_right _ _) hOut2 (Finset.Subset.refl _))
      exact C.con_subset (EntSet.union_mem C hout hEntt2) (funion.subset_right _ _)
    refine ⟨hs, htt', hw, s1 ∪' s2, hsub, ?_, ?_⟩
    · intro q hq
      rcases funion.mem.mp hq with hq | hq
      · exact hIn1 q hq
      · exact hIn2 q hq
    · rw [funOutputUnion.funion]
      exact EntSet.union C
        (EntSet.mono C (C.con_subset hout (funion.subset_left _ _)) hout
          (funion.subset_left _ _) hOut1 (Finset.Subset.refl _))
        (EntSet.mono C (C.con_subset hout (funion.subset_right _ _)) hout
          (funion.subset_right _ _) hOut2 (Finset.Subset.refl _))
  mono := by
    rintro s s' t t' ⟨hs, ht, hEnt⟩ hEnts hEntt hs' ht'
    refine ⟨hs', ht', ?_⟩
    have hfst := ProdEnt.entSet_fst (functionSystem B C) B hEnts
    have hsnd := ProdEnt.entSet_snd (functionSystem B C) B hEnts
    have htok :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s)
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) := hEnt
    have hmid :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s')
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) :=
      (functionSystem B C).ent_trans hs'.1 hs.1 (fun y hy => hfst y hy) htok
    obtain ⟨hw', s1, hs1, hIn1, hOut1⟩ := hmid
    have hIn1' : ∀ q ∈ s1, B.EntSet (sndFinset (functionSystem B C) B s') q.val.1 :=
      fun q hq => EntSet.trans B hs'.2 hs.2 hsnd (hIn1 q hq)
    have hin : funInputUnion B C s1 ∈ B.Con :=
      B.con_subset
        (EntSet.union_mem B hs'.2 (entSet_inputUnion_of_ent B C hIn1'))
        (funion.subset_right _ _)
    have hout : funOutputUnion B C s1 ∈ C.Con := hw' s1 hs1 hin
    refine ⟨hw', s1, hs1, hIn1', ?_⟩
    exact EntSet.trans C hout ht hOut1 hEntt

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def uncurryMap (k : ApproximableMap A (functionSystem B C)) :
    ApproximableMap (productSystem A B) C :=
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B))

end InfoSys

end DomainTheory.InformationSystems


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
        (EntSet.union_mem B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (funion.subset_right _ _)
    have hmid : h.rel (liftPair A B v (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h v hv t hps hin

    have hEntIn : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      EntSet.trans B (hsnd.1.2) hin
        (EntSet.trans B (hsnd.1.2) hCon.2 hsnd.2.2
          (entSet_inputUnion_of_ent B C hIn))
        (EntSet.refl B hin)

    have hs : s ∈ (productSystem A B).Con := hfst.1
    have hEntv : A.EntSet (fstFinset A B s) v := hfst.2.2
    have hEntsnd : B.EntSet (sndFinset A B s) (sndFinset (functionSystem B C) B m) := hsnd.2.2
    have hEntIn' : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      EntSet.trans B hs.2 hin
        (EntSet.trans B hs.2 hCon.2 hEntsnd (entSet_inputUnion_of_ent B C hIn))
        (EntSet.refl B hin)
    have hdom : liftPair A B (fstFinset A B s) (sndFinset A B s) ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hs.1 hs.2

    have hmid' : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s))
        (funOutputUnion B C t) :=
      h.mono hmid (entSet_liftPair A B hs.1 hs.2 hEntv hEntIn')
        (EntSet.refl C (h.rel_cod hmid)) hdom (h.rel_cod hmid)

    have hEntLift : (productSystem A B).EntSet s (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
      intro p hp
      unfold liftPair at hp
      rcases funion.mem.mp hp with hp | hp
      · rcases (liftLeft.mem A B).1 hp with ⟨a, ha, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_refl hs.1 ha
        · intro _
          exact B.ent_bot hs.2
      · rcases (liftRight.mem A B).1 hp with ⟨b, hb, rfl⟩
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
            exact funion.subset_right _ _ hb
          exact B.ent_refl hLiftCon.2 hb'
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · have ha : p.val.1 ∈ fstFinset A B s :=
            (mem_fstFinset A B).2 ⟨p, hp, hL, rfl⟩
          have ha' : p.val.1 ∈
              fstFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [fstFinset_liftPair]
            exact funion.subset_left _ _ ha
          exact A.ent_refl hLiftCon.1 ha'
        · rw [hL]; exact B.ent_bot hLiftCon.2
    have hrel : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s)) w :=
      h.mono hh hEntLift (EntSet.refl C hw) hLiftCon hw
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
      rw [fstFinset.funion, liftLeft.fstFinset_eq]
    have hsnd_m : sndFinset (functionSystem B C) B m =
        sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
          sndFinset A B s := by
      change sndFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [sndFinset.funion, liftRight.sndFinset_eq]
    have hcurry_fst : (curryMap A B C h).rel (fstFinset A B s)
        (fstFinset (functionSystem B C) B m) := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have hp' : p ∈ {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
        rw [hfst_m] at hp
        exact hp
      rcases funion.mem.mp hp' with hp' | hp'
      · have : p = tok := Finset.mem_singleton.mp hp'
        subst this
        exact hrel
      · have hpbot : p = (functionSystem B C).bot :=
          Finset.mem_singleton.mp
            (liftRight.fstFinset_eq (functionSystem B C) B (sndFinset A B s) hp')
        subst hpbot
        change h.rel (liftPair A B (fstFinset A B s) (funBot B C).val.1) (funBot B C).val.2
        simp only [funBot]
        exact h.mono h.empty_rel (EntSet.empty (productSystem A B) _)
          (EntSet.empty C ∅) (ProdCon_liftPair A B hs.1 B.con_empty) C.con_empty
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    ·
      exact ⟨fstFinset A B s, ⟨hs, hs.1, EntSet.refl A hs.1⟩, hcurry_fst⟩
    ·
      refine ⟨hs, hmCon.2, ?_⟩
      intro b hb
      have hb' : b ∈
          sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
            sndFinset A B s := by
        rwa [hsnd_m] at hb
      rcases funion.mem.mp hb' with hb' | hb'
      · have : b = B.bot := Finset.mem_singleton.mp
          (liftLeft.sndFinset_eq (functionSystem B C) B {tok} hb')
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
          exact funion.subset_left _ _ (Finset.mem_singleton_self _)
        exact this
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        intro b hb
        have : b ∈ sndFinset (functionSystem B C) B m := by
          rw [hsnd_m]
          exact funion.subset_right _ _ hb
        exact B.ent_refl hmCon.2 this
      · rw [funOutputUnion.singleton]
        exact EntSet.refl C hw

end InfoSys
end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem applyMap_toElement (g : (functionSystem B C).Element) (y : B.Element) :
    (applyMap (B := B) (C := C)).toElement
      (pairElements (functionSystem B C) B g y) =
      (element_toApproxMap B C g).toElement y := by
  apply le_antisymm
  · intro Z ⟨s, hs, ⟨hCon, hZcon, hEnt⟩⟩
    obtain ⟨hw, t, ht, hIn, hOut⟩ := hEnt
    have ht_sub : ↑t ⊆ g.carrier := by
      intro p hp
      exact mem_fst_of_subset_pairElements (functionSystem B C) B hs (ht (Finset.mem_coe.1 hp))
    have hsnd_sub : ↑(sndFinset (functionSystem B C) B s) ⊆ y.carrier := by
      intro b hb
      exact mem_snd_of_subset_pairElements (functionSystem B C) B hs hb
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (EntSet.union_mem B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (funion.subset_right _ _)
    have hin_sub : ↑(funInputUnion B C t) ⊆ y.carrier := by
      intro b hb
      rcases (mem_funInputUnion B C).1 (Finset.mem_coe.1 hb) with ⟨q, hq, hb'⟩
      exact y.closed _ b hsnd_sub (hIn q hq b hb')
    have hEntZ : FunEnt B C t
        (mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z)) := by
      refine ⟨fun s' hs' hin' => hw s' (fun q hq => ht (hs' hq)) hin', t, Finset.Subset.refl _, ?_, hOut⟩
      intro q hq y' hy'
      exact B.ent_refl hin ((mem_funInputUnion B C).2 ⟨q, hq, hy'⟩)
    have hmem : mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z) ∈ g.carrier :=
      g.closed t _ ht_sub hEntZ
    exact ⟨funInputUnion B C t, hin_sub, ⟨hin, C.con_sing Z, hmem⟩⟩
  · intro Z ⟨v, hv, ⟨hvCon, hZcon, hmem⟩⟩
    let p : FunToken B C := mkFunToken B C v {Z} hvCon hZcon
    have hp : p ∈ g.carrier := hmem
    let s := liftPair (functionSystem B C) B {p} v
    have hsCon : ProdCon (functionSystem B C) B s :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing p) hvCon
    have hs_sub : ↑s ⊆ (pairElements (functionSystem B C) B g y).carrier :=
      subset_pairElements_liftPair (functionSystem B C) B
        (by
          intro q hq
          have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
          subst this
          exact hp)
        hv
    refine ⟨s, hs_sub, ⟨hsCon, C.con_sing Z, ?_⟩⟩
    refine ⟨?_, {p}, ?_, ?_, ?_⟩
    ·
      intro t ht hin
      have ht_sub : ↑t ⊆ g.carrier := by
        intro q hq
        exact mem_fst_of_subset_pairElements (functionSystem B C) B hs_sub (ht hq)
      exact (funCon_of_approxMap B C (element_toApproxMap B C g) t
        (fun q hq => ⟨q.property.1, q.property.2, by
          simpa [mkFunToken.eq] using ht_sub (Finset.mem_coe.2 hq)⟩)) t (Finset.Subset.refl _) hin
    ·
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      rw [show s = liftLeft (functionSystem B C) B {p} ∪' liftRight (functionSystem B C) B v from rfl]
      rw [fstFinset.funion, liftLeft.fstFinset_eq]
      exact funion.subset_left _ _ (Finset.mem_singleton_self _)
    ·
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      intro b hb
      have hb' : b ∈ v := hb

      have : b ∈ sndFinset (functionSystem B C) B s := by
        rw [sndFinset_liftPair]
        exact funion.subset_right _ _ hb'
      exact B.ent_refl hsCon.2 this
    ·
      rw [funOutputUnion.singleton]
      exact EntSet.refl C (C.con_sing Z)

end InfoSys
end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem curryMap_unique (h : ApproximableMap (productSystem A B) C)
    (k : ApproximableMap A (functionSystem B C))
    (huniv : uncurryMap A B C k = h) :
    k = curryMap A B C h := by
  have hk : uncurryMap A B C k = uncurryMap A B C (curryMap A B C h) := by
    rw [huniv, uncurry_curryMap]
  refine (ext_iff_toElement k (curryMap A B C h)).2 fun x => ?_
  have happly : ∀ y : B.Element,
      (element_toApproxMap B C (k.toElement x)).toElement y =
        (element_toApproxMap B C ((curryMap A B C h).toElement x)).toElement y := by
    intro y
    have hpair_k :
        (pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B (k.toElement x) y := by
      apply productSystem.element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (productSystem.fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = k.toElement x := by
          rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements]
        exact h1.trans (fstMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
      · have h1 : (productSystem.sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
        exact h1.trans (sndMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
    have hpair_c :
        (pairMap (functionSystem B C) B
            (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y := by
      apply productSystem.element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (productSystem.fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = (curryMap A B C h).toElement x := by
          rw [← comp.toElement, pairMap.comp_fst, comp.toElement, fstMap_pairElements]
        exact h1.trans
          (fstMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
      · have h1 : (productSystem.sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (productSystem.fstMap A B)) (productSystem.sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]
        exact h1.trans
          (sndMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
    have hu1 : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B (k.toElement x) y) := by
      simp only [uncurryMap, comp.toElement, hpair_k]
    have hu2 : (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y) := by
      simp only [uncurryMap, comp.toElement, hpair_c]
    have heq : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) := by
      rw [hk]
    rw [← applyMap_toElement, ← applyMap_toElement, ← hu1, ← hu2, heq]
  have hx : element_toApproxMap B C (k.toElement x) =
      element_toApproxMap B C ((curryMap A B C h).toElement x) :=
    (ext_iff_toElement _ _).2 happly
  have : k.toElement x = (curryMap A B C h).toElement x := by
    rw [← approxMap_toElement_element_toApproxMap B C (k.toElement x),
      ← approxMap_toElement_element_toApproxMap B C ((curryMap A B C h).toElement x), hx]
  rw [this]

end InfoSys
end DomainTheory.InformationSystems
