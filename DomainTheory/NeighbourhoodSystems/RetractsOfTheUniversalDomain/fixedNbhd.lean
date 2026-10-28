module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

abbrev FixSet (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

instance instNonemptyMemSubtype (x : V.Element) : Nonempty {X : Set γ // x.mem X} :=
  ⟨⟨V.master, x.master_mem⟩⟩

def IsCompactElt (x : V.Element) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k),
    x ≤ iSupDirected d hdir → ∃ i, x ≤ d i

theorem principal_le_of_mem {y : V.Element} {Z : Set γ} (hZ : y.mem Z) :
    V.principal (y.sub hZ) ≤ y :=
  fun _ ⟨hW, hZW⟩ => y.up_mem hZ hW hZW

theorem principalFamily_directed (x : V.Element) :
    ∀ i j : {X : Set γ // x.mem X}, ∃ k : {X : Set γ // x.mem X},
      V.principal (x.sub i.2) ≤ V.principal (x.sub k.2) ∧
        V.principal (x.sub j.2) ≤ V.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

theorem eq_iSupDirected_principal (x : V.Element) :
    x = iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

theorem eq_principal_of_isCompactElt {x : V.Element} (hx : IsCompactElt x) :
    ∃ (X : Set γ) (hX : V.mem X), x = V.principal hX := by
  have hle : x ≤ iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := le_of_eq (eq_iSupDirected_principal x)
  obtain ⟨i0, hi0⟩ :=
    hx (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2)) (principalFamily_directed x) hle
  exact ⟨i0.1, x.sub i0.2, le_antisymm hi0 (principal_le_of_mem i0.2)⟩

theorem principal_compact {X : Set γ} (hX : V.mem X) {I : Type*} [Nonempty I]
    (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
    (h : V.principal hX ≤ iSupDirected d hdir) : ∃ i, V.principal hX ≤ d i := by
  obtain ⟨i, hi⟩ := (mem_iSupDirected d hdir).mp (h X ⟨hX, subset_rfl⟩)
  exact ⟨i, fun _ ⟨hW, hXW⟩ => (d i).up_mem hi hW hXW⟩

theorem principal_isCompactElt {X : Set γ} (hX : V.mem X) : IsCompactElt (V.principal hX) :=
  fun d hdir h => principal_compact hX d hdir h

end Algebraic

theorem fixedNbhd_subsystem (a : ApproximableMap E E) : fixedNbhd a ◁ E where
  master_eq := rfl
  sub := fun h => h.1
  inter_closed := by
    rintro X Y ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ hEXY
    have h1 : a.rel (X ∩ Y) X := a.mono hXa Set.inter_subset_left subset_rfl hEXY hXE
    have h2 : a.rel (X ∩ Y) Y := a.mono hYa Set.inter_subset_right subset_rfl hEXY hYE
    exact ⟨hEXY, a.inter_right h1 h2⟩

theorem mem_of_exists_rel_self {a : ApproximableMap E E} (x : E.Element) {Y : Set α}
    (hYE : E.mem Y) {X : Set α} (hXx : x.mem X) (hXY : X ⊆ Y) (hXaX : a.rel X X) :
    (a.toElementMap x).mem Y := by
  have hX : E.mem X := a.rel_dom hXaX
  have hmem : (a.toElementMap (E.principal hX)).mem X := (a.rel_iff_mem_principal hX).mp hXaX
  have hle : E.principal hX ≤ x := principal_le_of_mem hXx
  have hXmem : (a.toElementMap x).mem X := (a.toElementMap_mono hle) X hmem
  exact (a.toElementMap x).up_mem hXmem hYE hXY

theorem isFinitaryProjection_of_formula (a : ApproximableMap E E)
    (hii : ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) :
    FinitaryProjection a := by
  have heq : a = Subsystem.retractionOfSubsystem (fixedNbhd_subsystem a) := by
    apply ApproximableMap.ext
    intro X Z
    rw [Subsystem.retractionOfSubsystem_rel]
    constructor
    · intro hr
      have hX : E.mem X := a.rel_dom hr
      have hmem : (a.toElementMap (E.principal hX)).mem Z := (a.rel_iff_mem_principal hX).mp hr
      obtain ⟨hZE, Y, hXY, hYZ, hYa⟩ := hii (E.principal hX) |>.mp hmem
      exact ⟨hX, hZE, Y, ⟨a.rel_dom hYa, hYa⟩, (E.mem_principal hX).mp hXY |>.2, hYZ⟩
    · rintro ⟨hX, hZ, Y, ⟨_, hYa⟩, hXY, hYZ⟩
      exact (a.rel_iff_mem_principal hX).mpr
        (mem_of_exists_rel_self (E.principal hX) hZ (E.mem_principal hX |>.mpr ⟨a.rel_dom hYa, hXY⟩)
          hYZ hYa)
  rw [heq]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem a)

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

def sectionMap : ApproximableMap F E :=
  ofMono (fun _X hX => (e.symm (F.principal hX)).1) (fun _ _ hX hX' hXX' =>
    e.symm.monotone ((F.principal_le_iff hX hX').mpr hXX'))

theorem toElementMap_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i) :
    a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir := by
  rw [toElementMap_iSupDirected]
  apply Element.ext
  intro Z
  rw [mem_iSupDirected, mem_iSupDirected]
  simp_rw [hfix]

@[simp] theorem toElementMap_sectionMap_principal {X : Set β} (hX : F.mem X) :
    (sectionMap e).toElementMap (F.principal hX) = (e.symm (F.principal hX)).1 :=
  toElementMap_ofMono_principal _ _ X hX

theorem toElementMap_sectionMap (w' : F.Element) :
    (sectionMap e).toElementMap w' = (e.symm w').1 := by
  have hdirC : ∀ i j : {X : Set β // w'.mem X}, ∃ k : {X : Set β // w'.mem X},
      (e.symm (F.principal (w'.sub i.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 ∧
        (e.symm (F.principal (w'.sub j.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 :=
    fun i j => ⟨⟨i.1 ∩ j.1, w'.inter_mem i.2 j.2⟩,
      e.symm.monotone ((F.principal_le_iff (w'.sub i.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_left),
      e.symm.monotone ((F.principal_le_iff (w'.sub j.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_right)⟩
  have hS_eq : (sectionMap e).toElementMap w' =
      iSupDirected (fun i : {X : Set β // w'.mem X} => (e.symm (F.principal (w'.sub i.2))).1)
        hdirC := by
    apply Element.ext
    intro Z
    rw [toElementMap_mem_iff_principal, mem_iSupDirected]
    constructor
    · rintro ⟨X, hX, hZ⟩; rw [toElementMap_sectionMap_principal] at hZ; exact ⟨⟨X, hX⟩, hZ⟩
    · rintro ⟨⟨X, hX⟩, hZ⟩; exact ⟨X, hX, by rwa [toElementMap_sectionMap_principal]⟩
  have hfixC : ∀ i : {X : Set β // w'.mem X},
      a.toElementMap (e.symm (F.principal (w'.sub i.2))).1 =
        (e.symm (F.principal (w'.sub i.2))).1 :=
    fun i => (e.symm (F.principal (w'.sub i.2))).2
  apply le_antisymm
  · rw [hS_eq]
    apply iSupDirected_le
    intro i
    exact e.symm.monotone (principal_le_of_mem i.2)
  · have hSfix : a.toElementMap ((sectionMap e).toElementMap w') =
        (sectionMap e).toElementMap w' := by
      rw [hS_eq]; exact toElementMap_iSupDirected_fixed _ hdirC hfixC
    have key : w' ≤ e ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
      refine le_trans (le_of_eq (eq_iSupDirected_principal w'))
        (iSupDirected_le _ (principalFamily_directed w') ?_)
      intro i
      have : e.symm (F.principal (w'.sub i.2)) ≤ ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
        show (e.symm (F.principal (w'.sub i.2))).1 ≤ (sectionMap e).toElementMap w'
        rw [hS_eq]
        exact le_iSupDirected _ hdirC i
      have := e.monotone this
      rwa [e.apply_symm_apply] at this
    have := e.symm.monotone key
    rwa [e.symm_apply_apply] at this

theorem e_apply_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i)
    (hSfix : a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir)
    (hdir' : ∀ i j : I, ∃ k, e ⟨d i, hfix i⟩ ≤ e ⟨d k, hfix k⟩ ∧
      e ⟨d j, hfix j⟩ ≤ e ⟨d k, hfix k⟩) :
    e ⟨iSupDirected d hdir, hSfix⟩ = iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' := by
  apply le_antisymm
  · have hstep : (⟨iSupDirected d hdir, hSfix⟩ : FixSet a) ≤
        e.symm (iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir') := by
      show iSupDirected d hdir ≤ _
      apply iSupDirected_le
      intro i
      show d i ≤ _
      have hle : e ⟨d i, hfix i⟩ ≤ iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' :=
        le_iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' i
      have := e.symm.monotone hle
      rwa [e.symm_apply_apply] at this
    have := e.monotone hstep
    rwa [e.apply_symm_apply] at this
  · apply iSupDirected_le
    intro i
    exact e.monotone (le_iSupDirected d hdir i)

theorem toElementMap_idem {a : ApproximableMap E E} (ha : Retraction a) (z : E.Element) :
    a.toElementMap (a.toElementMap z) = a.toElementMap z := by
  rw [← toElementMap_comp a a z, ha.out]

theorem exists_principal_eq_of_isRetraction_le_idMap (ha_ret : Retraction a)
    (ha_proj : a ≤ idMap E) {Y : Set β} (hY : F.mem Y) :
    ∃ (X : Set α) (hX : E.mem X), (e.symm (F.principal hY)).1 = E.principal hX := by
  apply eq_principal_of_isCompactElt
  intro I _ d hdir hle
  set d2 : I → E.Element := fun i => a.toElementMap (d i) with hd2
  have hdir2 : ∀ i j, ∃ k, d2 i ≤ d2 k ∧ d2 j ≤ d2 k := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩
  have hfix2 : ∀ i, a.toElementMap (d2 i) = d2 i := fun i => toElementMap_idem ha_ret (d i)
  have hle2 : (e.symm (F.principal hY)).1 ≤ iSupDirected d2 hdir2 := by
    calc (e.symm (F.principal hY)).1 = a.toElementMap (e.symm (F.principal hY)).1 :=
          (e.symm (F.principal hY)).2.symm
      _ ≤ a.toElementMap (iSupDirected d hdir) := a.toElementMap_mono hle
      _ = iSupDirected d2 hdir2 := toElementMap_iSupDirected a d hdir
  have hSfix2 : a.toElementMap (iSupDirected d2 hdir2) = iSupDirected d2 hdir2 :=
    toElementMap_iSupDirected_fixed d2 hdir2 hfix2
  have hdir2' : ∀ i j : I, ∃ k, e ⟨d2 i, hfix2 i⟩ ≤ e ⟨d2 k, hfix2 k⟩ ∧
      e ⟨d2 j, hfix2 j⟩ ≤ e ⟨d2 k, hfix2 k⟩ := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir2 i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  have hle3 : F.principal hY ≤ iSupDirected (fun i => e ⟨d2 i, hfix2 i⟩) hdir2' := by
    have h1 : e ⟨(e.symm (F.principal hY)).1, (e.symm (F.principal hY)).2⟩ ≤
        e ⟨iSupDirected d2 hdir2, hSfix2⟩ := e.monotone hle2
    rwa [Subtype.coe_eta, e.apply_symm_apply,
      e_apply_iSupDirected_fixed e d2 hdir2 hfix2 hSfix2 hdir2'] at h1
  obtain ⟨i0, hi0⟩ := principal_isCompactElt hY _ _ hle3
  have hi0' : e.symm (F.principal hY) ≤ ⟨d2 i0, hfix2 i0⟩ := by
    have := e.symm.monotone hi0
    rwa [e.symm_apply_apply] at this
  have hfinal : (e.symm (F.principal hY)).1 ≤ d2 i0 := hi0'
  have hd2le : d2 i0 ≤ d i0 := by
    have := (le_iff_toElementMap_le.mp ha_proj) (d i0)
    rwa [toElementMap_idMap] at this
  exact ⟨i0, hfinal.trans hd2le⟩

theorem formula_of_isFinitaryProjection {a : ApproximableMap E E} (h : FinitaryProjection a) :
    ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X := by
  obtain ⟨⟨ha_ret, ha_proj⟩, β, F, ⟨e⟩⟩ := h.out
  intro x Y
  constructor
  · intro hY
    have hw : a.toElementMap (a.toElementMap x) = a.toElementMap x := toElementMap_idem ha_ret x
    set w : E.Element := a.toElementMap x with hw_def
    have hYw : w.mem Y := hY
    have hclaim : (sectionMap e).toElementMap (e ⟨w, hw⟩) = w := by
      rw [toElementMap_sectionMap e (e ⟨w, hw⟩), e.symm_apply_apply]
    have hYsec : ((sectionMap e).toElementMap (e ⟨w, hw⟩)).mem Y := by rw [hclaim]; exact hYw
    obtain ⟨W, hW, hYW⟩ := (toElementMap_mem_iff_principal (sectionMap e) (e ⟨w, hw⟩)).mp hYsec
    rw [toElementMap_sectionMap_principal] at hYW
    obtain ⟨X, hX, hXeq⟩ :=
      exists_principal_eq_of_isRetraction_le_idMap e ha_ret ha_proj ((e ⟨w, hw⟩).sub hW)
    rw [hXeq] at hYW
    obtain ⟨hYE, hXY⟩ := (E.mem_principal hX).mp hYW
    have hfixX : a.toElementMap (E.principal hX) = E.principal hX := by
      rw [← hXeq]; exact (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).2
    have haXX : a.rel X X := (a.rel_iff_mem_principal hX).mpr (by
      rw [hfixX]; exact (E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    have hprincipal_le_w : E.principal hX ≤ w := by
      have h1 : F.principal ((e ⟨w, hw⟩).sub hW) ≤ e ⟨w, hw⟩ :=
        principal_le_of_mem hW
      have h2 : e.symm (F.principal ((e ⟨w, hw⟩).sub hW)) ≤ e.symm (e ⟨w, hw⟩) :=
        e.symm.monotone h1
      have h3 : (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).1 ≤ w := by
        have := h2
        rwa [e.symm_apply_apply] at this
      rwa [hXeq] at h3
    have hw_le_x : w ≤ x := by
      have := (le_iff_toElementMap_le.mp ha_proj) x
      rwa [toElementMap_idMap] at this
    have hXx : x.mem X := hprincipal_le_w.trans hw_le_x X ((E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    exact ⟨hYE, X, hXx, hXY, haXX⟩
  · rintro ⟨hYE, X, hXx, hXY, hXaX⟩
    exact mem_of_exists_rel_self x hYE hXx hXY hXaX

end HardDirection

end

end DomainTheory.NeighbourhoodSystems
