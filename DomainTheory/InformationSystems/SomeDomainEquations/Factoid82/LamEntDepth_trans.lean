module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_fun
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_funion_of_entSet
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_of_ent

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Def 2.1 `ent_trans`: cases on the RHS token (Scott’s turnstile advice). -/
theorem LamEntDepth_trans {u v : Finset (RawLamToken α)} {c : RawLamToken α}
    (hv : LamConDepth A v) (hu : LamConDepth A u)
    (hEnts : ∀ t ∈ u, LamEntDepth A v t) (ht : LamEntDepth A u c) :
    LamEntDepth A v c := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ M u v c,
      Nat.max (finsetMaxDepth v) (Nat.max (finsetMaxDepth u) (rawDepth c)) = M →
      LamConDepth A v → LamConDepth A u →
      (∀ t ∈ u, LamEntDepth A v t) → LamEntDepth A u c → LamEntDepth A v c from
    this _ u v c rfl hv hu hEnts ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u v c hM hv hu hEnts ht
    have hleV : finsetMaxDepth v ≤ M := by rw [← hM]; exact Nat.le_max_left _ _
    have hleU : finsetMaxDepth u ≤ M := by
      rw [← hM]; exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hleC : rawDepth c ≤ M := by
      rw [← hM]; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    -- (8) bot
    match c with
    | .bot => exact LamEntDepth.bot hv
    -- (10) atom
    | .atom x =>
      cases ht with
      | @atom u x hu' hF hne hEnt =>
        obtain ⟨y0, hy0⟩ := Finset.nonempty_of_ne_empty hne
        have hEy0 := hEnts _ (mem_lamAtomFinset.1 hy0)
        have hFv : lamFunFinset v = ∅ := by
          cases hEy0 with
          | atom _ hFv' _ _ => exact hFv'
        have hneV : lamAtomFinset v ≠ ∅ := by
          cases hEy0 with
          | atom _ _ hneV _ => exact hneV
        have hAtomEnt : ∀ y ∈ lamAtomFinset u, A.Ent (lamAtomFinset v) y := by
          intro y hy
          have hEy := hEnts _ (mem_lamAtomFinset.1 hy)
          cases hEy with
          | atom _ _ _ hE => exact hE
        exact LamEntDepth.atom hv hFv hneV
          (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
            ((LamConDepth_of_fun_empty A hF).1 hu') hAtomEnt hEnt)
    -- (11) funTok
    | .funTok xs ys =>
      cases ht with
      | @funTok u xs ys s hu' hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
        obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hWorld
        have hEp0 := hEnts _ (mem_lamFunFinset.1 hp0)
        have hAv : lamAtomFinset v = ∅ := by
          cases hEp0 with
          | funTok _ hAv' _ _ _ _ _ _ _ => exact hAv'
        have hFv : lamFunFinset v ≠ ∅ := by
          cases hEp0 with
          | funTok _ _ _ _ _ hFv' _ _ _ => exact hFv'
        have hWit : ∀ p ∈ s, ∃ s_p ⊆ lamFunFinset v,
            LamConDepth A (listToFinset p.1) ∧ LamConDepth A (listToFinset p.2) ∧
            (∀ r ∈ s_p, ∀ z ∈ listToFinset r.1, LamEntDepth A (listToFinset p.1) z) ∧
            (∀ z ∈ listToFinset p.2, LamEntDepth A (lamOutputUnion s_p) z) := by
          intro p hp
          have hEp := hEnts _ (mem_lamFunFinset.1 (hs hp))
          cases hEp with
          | @funTok _ _ _ s_p _ _ hCi hCo hs_p _ _ hEi hEo =>
            exact ⟨s_p, hs_p, hCi, hCo, hEi, hEo⟩
        -- Combined witness by Finset.induction_on (choice-free; avoid erase/card)
        have hComb : ∀ (s' : Finset (List (RawLamToken α) × List (RawLamToken α))),
            s' ⊆ s →
            ∃ S ⊆ lamFunFinset v,
              (∀ r ∈ S, ∀ z ∈ listToFinset r.1, LamEntDepth A (listToFinset xs) z) ∧
              (∀ z ∈ lamOutputUnion s', LamEntDepth A (lamOutputUnion S) z) ∧
              LamConDepth A (lamOutputUnion S) := by
          intro s'
          induction s' using Finset.induction_on with
          | empty =>
            intro _
            refine ⟨(∅ : Finset (List (RawLamToken α) × List (RawLamToken α))),
              Finset.empty_subset _, ?_, ?_, ?_⟩
            · intro _ hr; exact False.elim (Finset.notMem_empty _ hr)
            · intro z hz
              rw [lamOutputUnion_empty] at hz
              exact False.elim (Finset.notMem_empty z hz)
            · rw [lamOutputUnion_empty]; exact LamConDepth_empty A
          | insert q sR hq ihS =>
            intro hs'
            have hsR : sR ⊆ s := fun p hp => hs' (Finset.mem_insert_of_mem hp)
            have hqS : q ∈ s := hs' (Finset.mem_insert_self q sR)
            obtain ⟨S', hS'sub, hS'in, hS'out, hConS'⟩ := ihS hsR
            obtain ⟨Sq, hSqsub, hConQIn, hConQOut, hSqin, hSqout⟩ := hWit q hqS
            have hSsub : S' ∪' Sq ⊆ lamFunFinset v :=
              funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩
            have hEntAll : ∀ t ∈ lamInputUnion (S' ∪' Sq),
                LamEntDepth A (listToFinset xs) t := by
              intro t ht
              rcases (mem_lamInputUnion).1 ht with ⟨r, hr, ht'⟩
              rcases mem_funion.1 hr with hr | hr
              · exact hS'in r hr t ht'
              · refine ih _ ?_ (listToFinset q.1) (listToFinset xs) t rfl
                  hConIn hConQIn (fun w hw => hEntIn q hqS w hw) (hSqin r hr t ht')
                have htok : .funTok q.1 q.2 ∈ u := mem_lamFunFinset.1 (hs hqS)
                have htokR : .funTok r.1 r.2 ∈ v :=
                  mem_lamFunFinset.1 (hSsub (mem_funion.2 (Or.inr hr)))
                have hzt := rawDepth_funTok_gt_left (v := r.2) ((mem_listToFinset).1 ht')
                have hDq := (finsetMaxDepth_of_mem_funTok htok).1
                have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                  Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDq hleU,
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le hzt (le_finsetMaxDepth_of_mem htokR))
                      hleV⟩⟩
            have hinU : LamConDepth A (lamInputUnion (S' ∪' Sq)) :=
              LamConDepth_mono A (subset_funion_right _ _)
                (LamConDepth_funion_of_entSet A M
                  (fun _ _ _ hE => LamConDepth_insert_of_ent A hE)
                  hConIn hEntAll (fun t ht => by
                    rcases (mem_lamInputUnion).1 ht with ⟨r, hr, ht'⟩
                    have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                    have htok : .funTok r.1 r.2 ∈ v := mem_lamFunFinset.1 (hSsub hr)
                    exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                      Nat.lt_of_lt_of_le
                        (Nat.lt_of_lt_of_le
                          (rawDepth_funTok_gt_left (v := r.2) ((mem_listToFinset).1 ht'))
                          (le_finsetMaxDepth_of_mem htok)) hleV⟩))
            have hConU : LamConDepth A (lamOutputUnion (S' ∪' Sq)) :=
              ((LamConDepth_of_fun_nonempty A hFv).1 hv).2.2 (S' ∪' Sq) hSsub hinU
            have hConU' : LamConDepth A (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
              rw [← lamOutputUnion_funion]; exact hConU
            refine ⟨S' ∪' Sq, hSsub, ?_, ?_, hConU⟩
            · intro r hr z hz
              rcases mem_funion.1 hr with hr | hr
              · exact hS'in r hr z hz
              · exact hEntAll _ ((mem_lamInputUnion).2 ⟨r, mem_funion.2 (Or.inr hr), hz⟩)
            · intro z hz
              rw [lamOutputUnion_funion]
              have hz'' : z ∈ listToFinset q.2 ∪' lamOutputUnion sR := by
                rwa [lamOutputUnion_insert] at hz
              rcases mem_funion.1 hz'' with hzQ | hzR
              · have hzx := hSqout z hzQ
                have hsub := subset_funion_right (lamOutputUnion S') (lamOutputUnion Sq)
                cases decidableEq_finset
                    (lamFunFinset (lamOutputUnion S' ∪' lamOutputUnion Sq)) ∅ with
                | isFalse hFn =>
                  exact LamEntDepth_weaken_fun A hsub hConU'
                    ((LamConDepth_of_fun_nonempty A hFn).1 hConU').1 hzx
                | isTrue hFo =>
                  match z with
                  | .bot => exact LamEntDepth.bot hConU'
                  | .atom _ =>
                    exact LamEntDepth_weaken_atom A hsub hConU' hFo hzx
                  | .funTok _ _ =>
                    cases hzx with
                    | funTok _ _ _ _ _ hWo _ _ _ =>
                      exact False.elim (hWo (Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inr hp)
                          exact False.elim (Finset.notMem_empty p (hFo ▸ this)))
                        (Finset.empty_subset _)))
              · have hzx := hS'out z hzR
                have hsub := subset_funion_left (lamOutputUnion S') (lamOutputUnion Sq)
                cases decidableEq_finset
                    (lamFunFinset (lamOutputUnion S' ∪' lamOutputUnion Sq)) ∅ with
                | isFalse hFn =>
                  exact LamEntDepth_weaken_fun A hsub hConU'
                    ((LamConDepth_of_fun_nonempty A hFn).1 hConU').1 hzx
                | isTrue hFo =>
                  match z with
                  | .bot => exact LamEntDepth.bot hConU'
                  | .atom _ =>
                    exact LamEntDepth_weaken_atom A hsub hConU' hFo hzx
                  | .funTok _ _ =>
                    cases hzx with
                    | funTok _ _ _ _ _ hWo _ _ _ =>
                      exact False.elim (hWo (Finset.Subset.antisymm
                        (fun p hp => by
                          have : p ∈ lamFunFinset
                              (lamOutputUnion S' ∪' lamOutputUnion Sq) := by
                            rw [lamFunFinset_funion]
                            exact mem_funion.2 (Or.inl hp)
                          exact False.elim (Finset.notMem_empty p (hFo ▸ this)))
                        (Finset.empty_subset _)))
        obtain ⟨S, hSsub, hSin, hSoutS, hConS⟩ :=
          hComb s (Finset.Subset.refl _)
        have hConOutS : LamConDepth A (lamOutputUnion s) :=
          ((LamConDepth_of_fun_nonempty A hWorld).1 hu').2.2 s hs
            (LamConDepth_mono A (subset_funion_right _ _)
              (LamConDepth_funion_of_entSet A M
                (fun _ _ _ hE => LamConDepth_insert_of_ent A hE)
                hConIn
                (fun t ht => by
                  rcases (mem_lamInputUnion).1 ht with ⟨p, hp, ht'⟩
                  exact hEntIn p hp t ht')
                (fun t ht => by
                  rcases (mem_lamInputUnion).1 ht with ⟨p, hp, ht'⟩
                  have hDxs := finsetMaxDepth_list_lt_funTok xs ys
                  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
                  exact Nat.max_lt.2 ⟨Nat.lt_of_lt_of_le hDxs hleC,
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le
                        (rawDepth_funTok_gt_left ((mem_listToFinset).1 ht'))
                        (le_finsetMaxDepth_of_mem htok)) hleU⟩)))
        have hSout : ∀ z ∈ listToFinset ys, LamEntDepth A (lamOutputUnion S) z := by
          intro z hz
          refine ih _ ?_ (lamOutputUnion s) (lamOutputUnion S) z rfl
            hConS hConOutS (fun t ht => hSoutS t ht) (hEntOut z hz)
          exact Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le (finsetMaxDepth_outputUnion_lt hSsub hFv) hleV,
            Nat.max_lt.2 ⟨
              Nat.lt_of_lt_of_le (finsetMaxDepth_outputUnion_lt hs hWorld) hleU,
              Nat.lt_of_lt_of_le
                (rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)) hleC⟩⟩
        have hInCompat' : lamFunFinset (listToFinset xs) = ∅ →
            lamFunFinset (lamInputUnion S) = ∅ := by
          intro hxsF
          ext p
          constructor
          · intro hp
            have hmem : .funTok p.1 p.2 ∈ lamInputUnion S := mem_lamFunFinset.1 hp
            rcases (mem_lamInputUnion).1 hmem with ⟨r, hr, hr'⟩
            cases hSin r hr _ hr' with
            | funTok _ _ _ _ _ hWx _ _ _ => exact False.elim (hWx hxsF)
          · intro hp; exact False.elim (Finset.notMem_empty _ hp)
        exact LamEntDepth.funTok hv hAv hConIn hConOut hSsub hFv hInCompat' hSin hSout

end InfoSys

end DomainTheory.InformationSystems
