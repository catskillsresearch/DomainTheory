module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}
variable (P : ComputablePresentation D)

/- concordance: source L5161 EXERCISE 8.15 domain of subsystems — Fin(js) / SubD -/

/-- The sub-selection of `js` consisting of entries belonging to `sub1` or `sub2` — the `List`-level
"join" of two sub-selections, used to combine two consistent sub-meets into a third. -/
def combineSub (js sub1 sub2 : List ℕ) : List ℕ :=
  js.filter (fun j => decide (j ∈ sub1 ∨ j ∈ sub2))

theorem combineSub_sublist (js sub1 sub2 : List ℕ) :
    (combineSub js sub1 sub2).Sublist js := List.filter_sublist

theorem mem_combineSub {js sub1 sub2 : List ℕ} {j : ℕ} :
    j ∈ combineSub js sub1 sub2 ↔ j ∈ js ∧ (j ∈ sub1 ∨ j ∈ sub2) := by
  unfold combineSub
  rw [List.mem_filter, decide_eq_true_iff]

/-- **Combining two consistent sub-meets.** If `sub1, sub2 ⊑ js`, then `interFrom P D.master
(combineSub js sub1 sub2) = interFrom P D.master sub1 ∩ interFrom P D.master sub2` — a pure
set-theoretic fact about `interFrom`'s membership characterization (no consistency needed here). -/
theorem interFrom_combineSub_eq {js sub1 sub2 : List ℕ}
    (h1 : sub1.Sublist js) (h2 : sub2.Sublist js) :
    interFrom P D.master (combineSub js sub1 sub2) =
      interFrom P D.master sub1 ∩ interFrom P D.master sub2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom]
  constructor
  · rintro ⟨hzm, hall⟩
    exact ⟨⟨hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h1.subset hj, Or.inl hj⟩)⟩,
      hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h2.subset hj, Or.inr hj⟩)⟩
  · rintro ⟨⟨hzm, hall1⟩, _, hall2⟩
    refine ⟨hzm, fun j hj => ?_⟩
    obtain ⟨_, hj1 | hj2⟩ := mem_combineSub.mp hj
    · exact hall1 j hj1
    · exact hall2 j hj2

/-- **`Fin(js)`**: the finitely generated subsystem of `D` on the index list `js` — the set of
`D`-consistent "sub-meets" `interFrom P D.master sub` for sublists `sub ⊑ js`. Every member is
automatically a `D`-neighbourhood (the `D.mem Y` conjunct), so `finGen P js ⊆ D.mem` by
construction. -/
def finGen (js : List ℕ) : Set (Set α) :=
  {Y | ∃ sub : List ℕ, sub.Sublist js ∧ D.mem Y ∧ Y = interFrom P D.master sub}

/-- **Monotonicity.** A sublist generates a smaller (or equal) finitely generated subsystem. -/
theorem finGen_mono {js js' : List ℕ} (h : js.Sublist js') : finGen P js ⊆ finGen P js' :=
  fun _ ⟨sub, hsub, hD, hY⟩ => ⟨sub, hsub.trans h, hD, hY⟩

/-- Every member of `Fin(js)` is a `D`-neighbourhood. -/
theorem finGen_sub_mem {js : List ℕ} {Y : Set α} : Y ∈ finGen P js → D.mem Y :=
  fun ⟨_, _, hD, _⟩ => hD

/-- Every member of `Fin(js)` is a subset of `D.master`. -/
theorem finGen_sub_master {js : List ℕ} {Y : Set α} (h : Y ∈ finGen P js) : Y ⊆ D.master :=
  D.sub_master (finGen_sub_mem P h)

/-- `D.master ∈ Fin(js)` always (witness: the empty sub-selection). -/
theorem master_mem_finGen (js : List ℕ) : D.master ∈ finGen P js :=
  ⟨[], List.nil_sublist js, D.master_mem, rfl⟩

/-- The single-index generator `P.X i` lies in `Fin(js)` whenever `i ∈ js` (witness: the singleton
sub-selection `[i]`, always `D`-consistent since `interFrom P D.master [i] = D.master ∩ P.X i =
P.X i` using `P.X i ⊆ D.master`). -/
theorem principal_mem_finGen {js : List ℕ} {i : ℕ} (hi : i ∈ js) : P.X i ∈ finGen P js := by
  refine ⟨[i], (List.singleton_sublist).mpr hi, P.mem_X i, ?_⟩
  apply Set.ext
  intro z
  rw [mem_interFrom]
  constructor
  · intro hz
    exact ⟨D.sub_master (P.mem_X i) hz,
      fun j hj => by rw [List.mem_singleton] at hj; subst hj; exact hz⟩
  · rintro ⟨_, hall⟩
    exact hall i (List.mem_singleton.mpr rfl)

/-- **`Fin(js)` as a `NeighborhoodSystem`.** Master is `D.master`; closure under consistent
intersection combines the two witnessing sub-selections via `combineSub`. -/
def finGenSys (js : List ℕ) : NeighborhoodSystem α where
  mem Y := Y ∈ finGen P js
  master := D.master
  master_nonempty := D.master_nonempty
  master_mem := master_mem_finGen P js
  inter_mem := by
    rintro X Y Z ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ ⟨sub3, h3, hDZ, hZ⟩ hZsub
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2,
      D.inter_mem hDX hDY hDZ hZsub, by
        rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩
  sub_master := fun ⟨sub, _, _, hY⟩ => hY ▸ interFrom_subset P

@[simp] theorem mem_finGenSys {js : List ℕ} {Y : Set α} :
    (finGenSys P js).mem Y ↔ Y ∈ finGen P js := Iff.rfl

/-- **`Fin(js)` is a subsystem of `D`** (Definition 6.10). -/
theorem finGenSys_subsystem (js : List ℕ) : finGenSys P js ◁ D where
  master_eq := rfl
  sub := finGen_sub_mem P
  inter_closed := by
    rintro X Y ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ hXY
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2, hXY, by
      rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩

/-- `interFrom P A (j :: sub)` splits off the head as an intersection with `P.X j` — a pure
set-theoretic fact from `mem_interFrom`'s characterization. -/
theorem interFrom_cons_eq (A : Set α) (j : ℕ) (sub : List ℕ) :
    interFrom P A (j :: sub) = P.X j ∩ interFrom P A sub := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, List.forall_mem_cons]
  tauto

/-- **The workhorse lemma.** For any subsystem `D' ◁ D`, `Fin(js) ⊆ D'.mem` iff every single
generator `P.X i` (`i ∈ js`) already lies in `D'.mem`. Proved by induction on `js`: the `cons` step
uses `interFrom_mem_of_witness` (`Theorem75.lean`) to show that the "tail" sub-meet of a consistent
`j :: sub`-selection is itself consistent (using the *full* meet as witness), then combines via
`D'.inter_closed`. -/
theorem finGen_le_iff_forall_mem {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    finGen P js ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  induction js with
  | nil =>
    refine ⟨fun _ i hi => absurd hi List.not_mem_nil, fun _ => ?_⟩
    rintro Y ⟨sub, hsub, _, hYeq⟩
    rw [List.eq_nil_of_sublist_nil hsub] at hYeq
    rw [hYeq, show interFrom P D.master ([] : List ℕ) = D.master from rfl, ← hD'.master_eq]
    exact D'.master_mem
  | cons j js' ih =>
    rw [List.forall_mem_cons]
    constructor
    · intro hsub
      refine ⟨hsub (principal_mem_finGen P List.mem_cons_self), ?_⟩
      exact ih.mp ((finGen_mono P (List.sublist_cons_self j js')).trans hsub)
    · intro hall
      have hj := hall.1
      have hFinjs' : finGen P js' ⊆ D'.mem := ih.mpr hall.2
      rintro Y ⟨sub, hsub, hDY, hYeq⟩
      cases hsub with
      | cons _ hsub' => exact hFinjs' ⟨sub, hsub', hDY, hYeq⟩
      | cons_cons _ hsub' =>
        rename_i sub2
        rw [interFrom_cons_eq P D.master j sub2] at hYeq
        set Y2 := interFrom P D.master sub2 with hY2def
        have hY_sub_Y2 : Y ⊆ Y2 := hYeq ▸ Set.inter_subset_right
        have hDY2 : D.mem Y2 := interFrom_mem_of_witness P hDY hY_sub_Y2 D.master_mem
        have hY2mem : D'.mem Y2 := hFinjs' ⟨sub2, hsub', hDY2, rfl⟩
        have hXYmem : D.mem (P.X j ∩ Y2) := hYeq ▸ hDY
        exact hYeq ▸ hD'.inter_closed hj hY2mem hXYmem

/-- **The concatenation identity, general form.** For any subsystem `D' ◁ D`,
`Fin(js₁ ++ js₂) ⊆ D'.mem ↔ Fin(js₁) ⊆ D'.mem ∧ Fin(js₂) ⊆ D'.mem` — an immediate corollary of the
workhorse lemma via `List.forall_mem_append`. -/
theorem finGen_append_le_iff {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js1 js2 : List ℕ) :
    finGen P (js1 ++ js2) ⊆ D'.mem ↔ finGen P js1 ⊆ D'.mem ∧ finGen P js2 ⊆ D'.mem := by
  rw [finGen_le_iff_forall_mem P hD', finGen_le_iff_forall_mem P hD',
    finGen_le_iff_forall_mem P hD', List.forall_mem_append]

/-- **`nbhd(js)`**: the (anti-monotone) principal up-set of finite generators `js'` whose finitely
generated subsystem extends `Fin(js)` — the neighbourhood of `SubD` generated by `js`. -/
def nbhdGen (js : List ℕ) : Set (List ℕ) := {js' | finGen P js ⊆ finGen P js'}

@[simp] theorem mem_nbhdGen {js js' : List ℕ} :
    js' ∈ nbhdGen P js ↔ finGen P js ⊆ finGen P js' := Iff.rfl

/-- **Anti-monotonicity.** A bigger generator (`Fin`-wise) has a smaller up-set. -/
theorem nbhdGen_antitone {js js' : List ℕ} (h : finGen P js ⊆ finGen P js') :
    nbhdGen P js' ⊆ nbhdGen P js := fun _ hk => h.trans hk

theorem self_mem_nbhdGen (js : List ℕ) : js ∈ nbhdGen P js := (mem_nbhdGen P).mpr subset_rfl

/-- **The concatenation identity for `nbhd`.** `nbhd(js₁) ∩ nbhd(js₂) = nbhd(js₁ ++ js₂)` —
`finGen_append_le_iff` instantiated at `D' := finGenSys(js')` for each candidate `js'`. -/
theorem nbhdGen_inter (js1 js2 : List ℕ) :
    nbhdGen P js1 ∩ nbhdGen P js2 = nbhdGen P (js1 ++ js2) := by
  apply Set.ext
  intro js'
  simp only [mem_nbhdGen, Set.mem_inter_iff]
  exact (finGen_append_le_iff P (finGenSys_subsystem P js') js1 js2).symm

/-- **`SubD`: the reconstructed neighbourhood system.** Tokens are finite index lists (`List ℕ`,
representing finitely generated subsystems of `D`); neighbourhoods are the principal up-sets
`nbhd(js)`. -/
def SubD (P : ComputablePresentation D) : NeighborhoodSystem (List ℕ) where
  mem N := ∃ js, N = nbhdGen P js
  master := nbhdGen P []
  master_nonempty := ⟨[], self_mem_nbhdGen P []⟩
  master_mem := ⟨[], rfl⟩
  inter_mem := by
    rintro N1 N2 N3 ⟨js1, rfl⟩ ⟨js2, rfl⟩ ⟨js3, rfl⟩ _
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2⟩
  sub_master := by
    rintro N ⟨js, rfl⟩
    exact nbhdGen_antitone P (finGen_mono P (List.nil_sublist js))

/-- **Injectivity of `nbhd` on `Fin`.** `nbhd(a) = nbhd(b) → Fin(a) = Fin(b)`: evaluate the set
equality at `a` and at `b` (both reflexively self-membership) and combine by antisymmetry. -/
theorem finGen_eq_of_nbhdGen_eq {a b : List ℕ} (h : nbhdGen P a = nbhdGen P b) :
    finGen P a = finGen P b :=
  Set.Subset.antisymm ((Set.ext_iff.mp h b).mpr (self_mem_nbhdGen P b))
    ((Set.ext_iff.mp h a).mp (self_mem_nbhdGen P a))

/-- **`nbhd` equality is exactly `Fin` equality.** -/
theorem nbhdGen_eq_iff {a b : List ℕ} : nbhdGen P a = nbhdGen P b ↔ finGen P a = finGen P b := by
  refine ⟨finGen_eq_of_nbhdGen_eq P, fun h => ?_⟩
  unfold nbhdGen
  rw [h]

@[simp] theorem mem_SubD {N : Set (List ℕ)} : (SubD P).mem N ↔ ∃ js, N = nbhdGen P js := Iff.rfl

@[simp] theorem SubD_master : (SubD P).master = nbhdGen P [] := rfl


/-! ## Subsystem ↔ SubD.Element (order-iso building blocks) -/

/-- **The finite-fold lemma.** If every generator `P.X i` (`i ∈ js`) is individually confirmed by
`x` via some witness list, the witnesses can be concatenated (fold over the finite list `js`,
combining via `x.inter_mem`) into a *single* list `js₀` confirmed by `x` with `Fin(js) ⊆
Fin(js₀)`. -/
theorem exists_common_witness (x : (SubD P).Element) {js : List ℕ}
    (h : ∀ i ∈ js, ∃ js', x.mem (nbhdGen P js') ∧ P.X i ∈ finGen P js') :
    ∃ js0, x.mem (nbhdGen P js0) ∧ finGen P js ⊆ finGen P js0 := by
  induction js with
  | nil => exact ⟨[], SubD_master P ▸ x.master_mem, subset_rfl⟩
  | cons j js' ih =>
    obtain ⟨jsj, hxj, hjmem⟩ := h j List.mem_cons_self
    obtain ⟨js0', hx0', hsub0'⟩ := ih (fun i hi => h i (List.mem_cons_of_mem j hi))
    refine ⟨jsj ++ js0', nbhdGen_inter P jsj js0' ▸ x.inter_mem hxj hx0',
      (finGen_le_iff_forall_mem P (finGenSys_subsystem P (jsj ++ js0')) (j :: js')).mpr
        (List.forall_mem_cons.mpr ⟨?_, ?_⟩)⟩
    · exact finGen_mono P (List.sublist_append_left jsj js0') hjmem
    · exact fun i hi =>
        finGen_mono P (List.sublist_append_right jsj js0') (hsub0' (principal_mem_finGen P hi))


/-- **`interFrom` splits over list concatenation.** A pure membership-characterization fact
(`mem_interFrom` + `List.forall_mem_append`), independent of consistency. -/
theorem interFrom_append_eq (A : Set α) (l1 l2 : List ℕ) :
    interFrom P A (l1 ++ l2) = interFrom P A l1 ∩ interFrom P A l2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom, List.forall_mem_append]
  tauto


/-- **Forward direction: a subsystem induces a filter of `SubD`.** Given `D' ◁ D`, the filter
`ofSubsystem P D' hD'` consists of the neighbourhoods `nbhd(js)` such that `D'` already contains
every singleton generator `P.X i` for `i ∈ js`. -/
def ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) : (SubD P).Element where
  mem N := ∃ js, N = nbhdGen P js ∧ ∀ i ∈ js, D'.mem (P.X i)
  sub := fun ⟨js, hN, _⟩ => ⟨js, hN⟩
  master_mem := ⟨[], rfl, fun i hi => absurd hi List.not_mem_nil⟩
  inter_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl, h2⟩
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2, List.forall_mem_append.mpr ⟨h1, h2⟩⟩
  up_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl⟩ hsub
    have hle : finGen P js2 ⊆ finGen P js1 := hsub (self_mem_nbhdGen P js1)
    exact ⟨js2, rfl, (finGen_le_iff_forall_mem P hD' js2).mp
      (hle.trans ((finGen_le_iff_forall_mem P hD' js1).mpr h1))⟩

/-- **A reusable membership characterization**, generalizing the forward half of
`toSubsystem_ofSubsystem_mem`: for *any* `D' ◁ D`, `ofSubsystem P D' hD'` confirms `nbhd(js)`
exactly when `D'` confirms every generator in `js`. -/
theorem mem_ofSubsystem_nbhdGen {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    (ofSubsystem P D' hD').mem (nbhdGen P js) ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  constructor
  · rintro ⟨js', hjseq, hall⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    refine (finGen_le_iff_forall_mem P hD' js).mp ?_
    rw [hfin]
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall
  · exact fun hall => ⟨js, rfl, hall⟩


/-- **Backward direction: a filter of `SubD` induces a subsystem.** The neighbourhoods are the
`Fin(js)`-members for lists `js` confirmed by the filter `x`. -/
def toSubsystemSys (x : (SubD P).Element) : NeighborhoodSystem α where
  mem Y := ∃ js, x.mem (nbhdGen P js) ∧ Y ∈ finGen P js
  master := D.master
  master_nonempty := D.master_nonempty
  master_mem := ⟨[], x.master_mem, master_mem_finGen P []⟩
  inter_mem := by
    rintro X Y Z ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ ⟨js3, _, hZ⟩ hZsub
    have hDX := finGen_sub_mem P hX
    have hDY := finGen_sub_mem P hY
    have hDZ := finGen_sub_mem P hZ
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, D.inter_mem hDX hDY hDZ hZsub, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]
  sub_master := fun ⟨_, _, hY⟩ => finGen_sub_master P hY


/-- **`toSubsystemSys x` is a genuine subsystem of `D`.** Uses the same `interFrom_append_eq`
witness-combination argument as `inter_mem`, without needing the extra `Z`-witness. -/
theorem toSubsystemSys_subsystem (x : (SubD P).Element) : toSubsystemSys P x ◁ D where
  master_eq := rfl
  sub := fun ⟨_, _, hY⟩ => finGen_sub_mem P hY
  inter_closed := by
    rintro X Y ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ hXY
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, hXY, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]

/-- **Round trip 2.** `ofSubsystem P (toSubsystem P x).1 (toSubsystem P x).2 = x`. -/
theorem ofSubsystem_toSubsystem (x : (SubD P).Element) :
    ofSubsystem P (toSubsystemSys P x) (toSubsystemSys_subsystem P x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨js, rfl, hall⟩
    obtain ⟨js0, hx0, hsub0⟩ := exists_common_witness P x hall
    exact x.up_mem hx0 ⟨js, rfl⟩ (nbhdGen_antitone P hsub0)
  · intro hx
    obtain ⟨js, rfl⟩ := x.sub hx
    exact ⟨js, rfl, fun i hi => ⟨js, hx, principal_mem_finGen P hi⟩⟩

/-- **Membership transfer, filter form.** Combines round trip 2 with `mem_ofSubsystem_nbhdGen`:
a filter `x` confirms `nbhd(js)` exactly when the reconstructed subsystem `toSubsystemSys P x`
confirms every generator in `js`. The key bridge for `map_rel_iff'` below. -/
theorem mem_nbhdGen_iff (x : (SubD P).Element) (js : List ℕ) :
    x.mem (nbhdGen P js) ↔ ∀ i ∈ js, (toSubsystemSys P x).mem (P.X i) := by
  conv_lhs => rw [← ofSubsystem_toSubsystem P x]
  exact mem_ofSubsystem_nbhdGen P (toSubsystemSys_subsystem P x) js


/-- **The backward map, packaged as a subsystem.** -/
def toSubsystem (x : (SubD P).Element) : {D' : NeighborhoodSystem α // D' ◁ D} :=
  ⟨toSubsystemSys P x, toSubsystemSys_subsystem P x⟩

/-- **Round trip, membership form.** `toSubsystemSys (ofSubsystem D')` has exactly the same
neighbourhoods as `D'` itself. `→`: unwind the double existential via `nbhdGen_eq_iff` and the
workhorse lemma. `←`: `P.surj` finds an index `n` with `P.X n = Y`; the singleton list `[n]`
witnesses membership on both sides. -/
theorem toSubsystem_ofSubsystem_mem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) (Y : Set α) :
    (toSubsystemSys P (ofSubsystem P D' hD')).mem Y ↔ D'.mem Y := by
  constructor
  · rintro ⟨js, ⟨js', hjseq, hall⟩, hY⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall (hfin ▸ hY)
  · intro hY
    obtain ⟨n, hn⟩ := P.surj (hD'.sub hY)
    refine ⟨[n], ⟨[n], rfl, fun i hi => ?_⟩, hn ▸ principal_mem_finGen P (List.mem_singleton.mpr rfl)⟩
    rw [List.mem_singleton] at hi
    subst hi
    rw [hn]
    exact hY

/-- **Round trip 1.** `toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩`. -/
theorem toSubsystem_ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) :
    toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩ :=
  Subtype.ext (NeighborhoodSystem.ext (toSubsystem_ofSubsystem_mem P D' hD') hD'.master_eq.symm)


end DomainTheory.NeighbourhoodSystems
