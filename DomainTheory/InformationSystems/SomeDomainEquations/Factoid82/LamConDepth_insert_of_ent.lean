module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_fun
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.insert_filter_ne_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.filter_ne_subset_of_subset_insert_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_funion_of_entSet
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_assoc_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_comm_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_funion_le

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Prop 2.1(iii): inserting an entailed token preserves depth-Con. -/
theorem LamConDepth_insert_of_ent {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntDepth A u t) : LamConDepth A (insert t u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ M u t, Nat.max (finsetMaxDepth u) (rawDepth t) = M →
      LamEntDepth A u t → LamConDepth A (insert t u) from
    this _ _ _ rfl ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u t hM ht
    have ihIns : ∀ u' t', Nat.max (finsetMaxDepth u') (rawDepth t') < M →
        LamEntDepth A u' t' → LamConDepth A (insert t' u') :=
      fun u' t' hlt hEnt => ih _ hlt u' t' rfl hEnt
    match t with
    | .bot => exact LamConDepth_insert_bot A (LamEntDepth.con A ht)
    | .atom x => exact LamConDepth_insert_atom A ht
    | .funTok xs ys =>
      cases ht with
      | @funTok u xs ys s hu hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
        have hF' : lamFunFinset (insert (.funTok xs ys) u) ≠ ∅ := by
          rw [lamFunFinset_insert_funTok]
          exact Finset.insert_ne_empty _ _
        refine (LamConDepth_of_fun_nonempty A hF').2 ⟨?_, ?_, ?_⟩
        · rw [lamAtomFinset_insert_funTok]; exact hA
        · intro p hp
          rw [lamFunFinset_insert_funTok] at hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact ⟨hConIn, hConOut⟩
          · exact ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.1 p hp
        · intro sel hsel hIn
          if hp : (xs, ys) ∈ sel then
            let t' := sel.filter (· ≠ (xs, ys))
            have ht_eq : insert (xs, ys) t' = sel := insert_filter_ne_lam hp
            have ht'sub : t' ⊆ lamFunFinset u :=
              filter_ne_subset_of_subset_insert_lam (by
                intro q hq; have := hsel hq; rwa [lamFunFinset_insert_funTok] at this)
            have hin' : LamConDepth A (listToFinset xs ∪' lamInputUnion t') := by
              rwa [← ht_eq, lamInputUnion_insert] at hIn
            have hsub : s ∪' t' ⊆ lamFunFinset u :=
              funion_subset_iff.mpr ⟨hs, ht'sub⟩
            have hEnt_in_s : ∀ z ∈ lamInputUnion s,
                LamEntDepth A (listToFinset xs) z := by
              intro z hz
              rcases (mem_lamInputUnion).1 hz with ⟨p, hp', hz'⟩
              exact hEntIn p hp' z hz'
            have hEnt_big : ∀ z ∈ lamInputUnion s,
                LamEntDepth A (listToFinset xs ∪' lamInputUnion t') z := by
              intro z hz
              have hzx := hEnt_in_s z hz
              have hsubxs : listToFinset xs ⊆ listToFinset xs ∪' lamInputUnion t' :=
                subset_funion_left _ _
              cases decidableEq_finset
                  (lamFunFinset (listToFinset xs ∪' lamInputUnion t')) ∅ with
              | isFalse hFn =>
                have hAv := ((LamConDepth_of_fun_nonempty A hFn).1 hin').1
                exact LamEntDepth_weaken_fun A hsubxs hin' hAv hzx
              | isTrue hFhin =>
                match z with
                | .bot => exact LamEntDepth.bot hin'
                | .atom x =>
                  exact LamEntDepth_weaken_atom A hsubxs hin' hFhin hzx
                | .funTok xs1 ys1 =>
                  cases decidableEq_finset (lamFunFinset (listToFinset xs)) ∅ with
                  | isTrue hxsF =>
                    have hNoFun : lamFunFinset (lamInputUnion s) = ∅ := hInCompat hxsF
                    have hzmem : .funTok xs1 ys1 ∈ lamInputUnion s := hz
                    have : (xs1, ys1) ∈ lamFunFinset (lamInputUnion s) :=
                      mem_lamFunFinset.2 hzmem
                    rw [hNoFun] at this
                    exact False.elim (Finset.notMem_empty _ this)
                  | isFalse hxsF =>
                    have : lamFunFinset (listToFinset xs ∪' lamInputUnion t') ≠ ∅ := by
                      intro h
                      have : lamFunFinset (listToFinset xs) = ∅ :=
                        Finset.Subset.antisymm
                          (fun p hp => by
                            have hp' : p ∈ lamFunFinset
                                (listToFinset xs ∪' lamInputUnion t') := by
                              rw [lamFunFinset_funion]
                              exact mem_funion.2 (Or.inl hp)
                            rw [h] at hp'; exact False.elim (Finset.notMem_empty p hp'))
                          (Finset.empty_subset _)
                      exact hxsF this
                    exact False.elim (this hFhin)
            have hDt : rawDepth (.funTok xs ys) ≤ M := by
              rw [← hM]; exact Nat.le_max_right _ _
            have hDu : finsetMaxDepth u ≤ M := by
              rw [← hM]; exact Nat.le_max_left _ _
            have hxs_lt : finsetMaxDepth (listToFinset xs) < M :=
              Nat.lt_of_lt_of_le (finsetMaxDepth.list_lt_funTok xs ys) hDt
            have hys_lt : finsetMaxDepth (listToFinset ys) < M :=
              Nat.lt_of_lt_of_le (finsetMaxDepth.list_lt_funTok_out xs ys) hDt
            have bound_in : ∀ z ∈ lamInputUnion s,
                Nat.max (finsetMaxDepth (listToFinset xs ∪' lamInputUnion t'))
                  (rawDepth z) < M := by
              intro z hz
              have hDuBig : finsetMaxDepth (listToFinset xs ∪' lamInputUnion t') < M := by
                have hle := finsetMaxDepth_funion_le (listToFinset xs) (lamInputUnion t')
                refine Nat.lt_of_le_of_lt hle (Nat.max_lt.2 ⟨hxs_lt, ?_⟩)
                by_cases ht'e : t' = ∅
                · rw [ht'e, lamInputUnion_empty]
                  exact Nat.lt_of_le_of_lt (Nat.zero_le _) hxs_lt
                · obtain ⟨q, hq⟩ := Finset.nonempty_of_ne_empty ht'e
                  exact Nat.lt_of_lt_of_le
                    (finsetMaxDepth.inputUnion_lt ht'sub hWorld) hDu
              have hz_lt : rawDepth z < M := by
                rcases (mem_lamInputUnion).1 hz with ⟨p, hp', hz'⟩
                have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp')
                exact Nat.lt_of_lt_of_le
                  (Nat.lt_of_lt_of_le
                    (rawDepth_funTok_gt_left ((mem_listToFinset).1 hz'))
                    (le_finsetMaxDepth_of_mem htok))
                  hDu
              exact Nat.max_lt.2 ⟨hDuBig, hz_lt⟩
            have hbig : LamConDepth A
                ((listToFinset xs ∪' lamInputUnion t') ∪' lamInputUnion s) :=
              LamConDepth_funion_of_entSet A M ihIns hin' hEnt_big bound_in
            have hin_st' : LamConDepth A (lamInputUnion s ∪' lamInputUnion t') := by
              have heq :
                  (listToFinset xs ∪' lamInputUnion t') ∪' lamInputUnion s =
                    listToFinset xs ∪' (lamInputUnion s ∪' lamInputUnion t') := by
                rw [funion_assoc_lam, funion_comm_lam (lamInputUnion t')]
              have hbig' : LamConDepth A
                  (listToFinset xs ∪' (lamInputUnion s ∪' lamInputUnion t')) := by
                rwa [heq] at hbig
              exact LamConDepth_mono A (subset_funion_right _ _) hbig'
            have hin_union : LamConDepth A (lamInputUnion (s ∪' t')) := by
              rwa [lamInputUnion_funion]
            have hout_union : LamConDepth A
                (lamOutputUnion s ∪' lamOutputUnion t') := by
              have hout : LamConDepth A (lamOutputUnion (s ∪' t')) :=
                ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.2 (s ∪' t') hsub hin_union
              rwa [lamOutputUnion_funion] at hout
            have hEnt_out' : ∀ z ∈ listToFinset ys,
                LamEntDepth A (lamOutputUnion s ∪' lamOutputUnion t') z := by
              intro z hz
              have hzx := hEntOut z hz
              have hsubO : lamOutputUnion s ⊆
                  lamOutputUnion s ∪' lamOutputUnion t' := subset_funion_left _ _
              cases decidableEq_finset
                  (lamFunFinset (lamOutputUnion s ∪' lamOutputUnion t')) ∅ with
              | isFalse hFn =>
                have hAv := ((LamConDepth_of_fun_nonempty A hFn).1 hout_union).1
                exact LamEntDepth_weaken_fun A hsubO hout_union hAv hzx
              | isTrue hFo =>
                match z with
                | .bot => exact LamEntDepth.bot hout_union
                | .atom x =>
                  exact LamEntDepth_weaken_atom A hsubO hout_union hFo hzx
                | .funTok xs1 ys1 =>
                  -- Ent out_s funTok needs fun out_s ≠ ∅, but out_s ⊆ atom-world union
                  cases hzx with
                  | funTok _ _ _ _ hsO hWo _ _ _ =>
                    have hOsF : lamFunFinset (lamOutputUnion s) = ∅ :=
                      Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion s ∪' lamOutputUnion t') := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inl hp)
                          rw [hFo] at this
                          exact False.elim (Finset.notMem_empty p this))
                        (Finset.empty_subset _)
                    exact False.elim (hWo hOsF)
            have bound_out : ∀ z ∈ listToFinset ys,
                Nat.max (finsetMaxDepth (lamOutputUnion s ∪' lamOutputUnion t'))
                  (rawDepth z) < M := by
              intro z hz
              have hDuOut : finsetMaxDepth
                  (lamOutputUnion s ∪' lamOutputUnion t') < M := by
                have hle := finsetMaxDepth_funion_le (lamOutputUnion s) (lamOutputUnion t')
                refine Nat.lt_of_le_of_lt hle (Nat.max_lt.2 ⟨?_, ?_⟩)
                · by_cases hs0 : s = ∅
                  · rw [hs0, lamOutputUnion_empty]
                    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hys_lt
                  · exact Nat.lt_of_lt_of_le
                      (finsetMaxDepth.outputUnion_lt hs hWorld) hDu
                · by_cases ht'e : t' = ∅
                  · rw [ht'e, lamOutputUnion_empty]
                    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hys_lt
                  · exact Nat.lt_of_lt_of_le
                      (finsetMaxDepth.outputUnion_lt ht'sub hWorld) hDu
              have hz_lt : rawDepth z < M :=
                Nat.lt_of_lt_of_le
                  (rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)) hDt
              exact Nat.max_lt.2 ⟨hDuOut, hz_lt⟩
            have hfinal : LamConDepth A
                ((lamOutputUnion s ∪' lamOutputUnion t') ∪' listToFinset ys) :=
              LamConDepth_funion_of_entSet A M ihIns hout_union hEnt_out' bound_out
            have hout_t : LamConDepth A
                (listToFinset ys ∪' lamOutputUnion t') := by
              have heq :
                  (lamOutputUnion s ∪' lamOutputUnion t') ∪' listToFinset ys =
                    lamOutputUnion s ∪' (listToFinset ys ∪' lamOutputUnion t') := by
                rw [funion_assoc_lam, funion_comm_lam (lamOutputUnion t')]
              have hfinal' : LamConDepth A
                  (lamOutputUnion s ∪' (listToFinset ys ∪' lamOutputUnion t')) := by
                rwa [heq] at hfinal
              exact LamConDepth_mono A (subset_funion_right _ _) hfinal'
            show LamConDepth A (lamOutputUnion sel)
            rwa [← ht_eq, lamOutputUnion_insert]
          else
            have hsel' : sel ⊆ lamFunFinset u := by
              intro p hp'
              have := hsel hp'
              rw [lamFunFinset_insert_funTok] at this
              rcases Finset.mem_insert.mp this with rfl | h
              · exact False.elim (hp hp')
              · exact h
            exact ((LamConDepth_of_fun_nonempty A hWorld).1 hu).2.2 sel hsel' hIn

end InfoSys

end DomainTheory.InformationSystems
