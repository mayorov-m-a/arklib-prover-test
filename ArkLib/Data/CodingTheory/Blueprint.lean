import Mathlib
import ArkLib

theorem Finset_enat_toNat_min_eq_min' (s : Finset ℕ) (h : s.Nonempty) : ENat.toNat s.min = s.min' h := by
  classical
  have hmin : ((s.min' h : ℕ) : ENat) = s.min := by
    simpa using (Finset.coe_min' (s := s) h)
  calc
    ENat.toNat s.min = ENat.toNat ((s.min' h : ℕ) : ENat) := by
      simpa [← hmin]
    _ = s.min' h := by
      simpa

theorem code_dist_le_minDist (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) : Code.dist C ≤ Code.minDist C := by
  classical
  -- Rewrite goal to explicit sInf comparison
  change sInf {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, ¬ u = v ∧ Δ₀(u, v) ≤ d}
      ≤ sInf {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, ¬ u = v ∧ Δ₀(u, v) = d}

  -- Define the two sets S1 (with equality) and S2 (with ≤)
  set S1 : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, ¬ u = v ∧ Δ₀(u, v) = d}
  set S2 : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, ¬ u = v ∧ Δ₀(u, v) ≤ d}
  change sInf S2 ≤ sInf S1

  -- S1 ⊆ S2
  have hsubset : S1 ⊆ S2 := by
    intro d hd
    rcases hd with ⟨u, hu, v, hv, hne, hEq⟩
    exact ⟨u, hu, v, hv, hne, by simpa [hEq]⟩

  -- Split on whether S1 is nonempty
  by_cases hne : S1.Nonempty
  · -- use that sInf S1 ∈ S1, hence also in S2
    have hmem : sInf S1 ∈ S2 := hsubset (Nat.sInf_mem hne)
    exact Nat.sInf_le hmem
  · -- If S1 is empty, S2 is empty too; both sInfs are 0
    have hS2empty' : ¬ S2.Nonempty := by
      intro h2
      rcases h2 with ⟨d, hd⟩
      rcases hd with ⟨u, hu, v, hv, huv, hle⟩
      exact hne ⟨Δ₀(u, v), ⟨u, hu, v, hv, huv, rfl⟩⟩
    have hS1empty : S1 = (∅ : Set ℕ) := (Set.not_nonempty_iff_eq_empty).mp hne
    have hS2empty : S2 = (∅ : Set ℕ) := (Set.not_nonempty_iff_eq_empty).mp hS2empty'
    simpa [hS1empty, hS2empty, Nat.sInf_empty]

theorem code_exists_pair_attains_distprime_toNat (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] (h : ¬ Subsingleton C) :
  ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = (Code.dist' C).toNat := by
  classical
  -- Define the finite set of pairwise Hamming distances for distinct pairs in C
  let P : Finset ℕ :=
    ((Finset.univ : Finset (C × C)).filter (fun p : C × C => p.1 ≠ p.2)).image
      (fun p => hammingDist p.1.1 p.2.1)
  -- From ¬ subsingleton, get a nontrivial pair in C, hence P is nonempty
  haveI : Nontrivial C := (not_subsingleton_iff_nontrivial).1 h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne C
  have hxymem : (x, y) ∈ ((Finset.univ : Finset (C × C)).filter (fun p : C × C => p.1 ≠ p.2)) := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simp, by simpa using hxy⟩
  have hPne : P.Nonempty := by
    refine ⟨hammingDist x.1 y.1, ?_⟩
    exact Finset.mem_image.mpr ⟨(x, y), hxymem, rfl⟩
  -- Let d0 be the minimum element of P; extract the corresponding pair (u,v)
  let d0 := P.min' hPne
  have hd0_mem : d0 ∈ P := Finset.min'_mem P hPne
  rcases Finset.mem_image.mp hd0_mem with ⟨p, hp, hp_eq⟩
  -- p is a distinct pair from C
  have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  -- The underlying functions are distinct as well
  have hcoe_ne : p.1.1 ≠ p.2.1 := by
    intro h'
    apply hp_ne
    apply Subtype.ext
    simpa using h'
  -- Conclude with u := p.1.1, v := p.2.1 and compute Code.dist'
  refine ⟨p.1.1, p.1.2, ?_⟩
  refine ⟨p.2.1, p.2.2, ?_, ?_⟩
  · exact hcoe_ne
  · -- Identify (Code.dist' C).toNat with d0, then use hp_eq
    have hmin_toNat : (Code.dist' C).toNat = d0 := by
      have h' : ENat.toNat (P.min) = d0 := by
        have := Finset_enat_toNat_min_eq_min' (s := P) hPne
        simpa [d0] using this
      simpa [Code.dist', P] using h'
    have : d0 = hammingDist p.1.1 p.2.1 := by simpa [P, d0] using hp_eq.symm
    simpa [this, hmin_toNat]

theorem code_dist_le_toNat_dist_prime (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] : Code.dist C ≤ (Code.dist' C).toNat := by
  classical
  by_cases hC : Subsingleton C
  · -- Subsingleton: dist is 0, so the inequality is trivial
    have hdist : Code.dist C = 0 := by simpa using Code.dist_subsingleton (C:=C)
    simpa [hdist] using (Nat.zero_le (Code.dist' C).toNat)
  · -- Non-subsingleton: pick a pair attaining (Code.dist' C).toNat
    obtain ⟨u, hu, v, hv, hne, hmin⟩ :=
      code_exists_pair_attains_distprime_toNat (n:=n) (R:=R) (C:=C) hC
    -- Unfold the definition of Code.dist and apply sInf_le using the minimizing pair
    change sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}
        ≤ (Code.dist' C).toNat
    refine Nat.sInf_le ?_
    refine ⟨u, hu, v, hv, hne, ?_⟩
    simpa [hmin] using (le_rfl : (Code.dist' C).toNat ≤ (Code.dist' C).toNat)

theorem code_minDist_le_pairDist (ι : Type*) [Fintype ι] (F : Type*) [DecidableEq F]
(C : Set (ι → F)) {u v : ι → F} (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
  Code.minDist C ≤ hammingDist u v := by
  classical
  change sInf {d : ℕ | ∃ u' ∈ C, ∃ v' ∈ C, u' ≠ v' ∧ hammingDist u' v' = d} ≤ hammingDist u v
  apply Nat.sInf_le
  exact ⟨u, hu, v, hv, hne, rfl⟩

theorem code_pairs_nonempty_of_not_subsingleton (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] (h : ¬ Subsingleton C) :
  (((@Finset.univ (C × C) _).filter (fun p : C × C => p.1 ≠ p.2))).Nonempty := by
  classical
  haveI : Nontrivial C := (not_subsingleton_iff_nontrivial).mp h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne C
  refine ⟨(x, y), ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · simpa

theorem code_toNat_distprime_le_pairDist (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C]
{u v : n → R} (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
  (Code.dist' C).toNat ≤ hammingDist u v := by
  classical
  -- Define the set of all pairwise Hamming distances of distinct codewords in C
  let s : Finset ℕ :=
    ((Finset.univ : Finset (C × C)).filter (fun p : C × C => p.1 ≠ p.2)).image
      (fun p : C × C => hammingDist p.1.1 p.2.1)
  -- The distinct pair (u,v) appears in the filtered universe
  let cu : C := ⟨u, hu⟩
  let cv : C := ⟨v, hv⟩
  have hneq_sub : cu ≠ cv := by
    intro h; apply hne; exact congrArg Subtype.val h
  have hmem_filter : (cu, cv) ∈ (Finset.univ : Finset (C × C)).filter (fun p : C × C => p.1 ≠ p.2) := by
    simp [Finset.mem_filter, hneq_sub]
  have hmem_s : hammingDist u v ∈ s := by
    -- show that (cu,cv) maps to hammingDist u v under the image map
    refine Finset.mem_image.mpr ?_;
    refine ⟨(cu, cv), hmem_filter, ?_⟩
    rfl
  -- hence s is nonempty
  have hne_s : s.Nonempty := ⟨_, hmem_s⟩
  -- Use the characterization of min' as a least element of the set
  have hmin_le : s.min' hne_s ≤ hammingDist u v := by
    have hleast : IsLeast (s : Set ℕ) (s.min' hne_s) := Finset.isLeast_min' (s := s) (H := hne_s)
    have hmem_coe : hammingDist u v ∈ (s : Set ℕ) := by simpa [Finset.mem_coe] using hmem_s
    exact hleast.2 hmem_coe
  -- Relate Code.dist' to s.min and then toNat to min'
  have h_toNat_min : (Code.dist' C).toNat = s.min' hne_s := by
    -- provided lemma converting ENat toNat of Finset.min to min' on nonempty sets
    have := Finset_enat_toNat_min_eq_min' s hne_s
    -- unfold the definition of Code.dist' to the min over s
    simpa [s, Code.dist'] using this
  -- conclude
  simpa [h_toNat_min] using hmin_le

theorem code_toNat_distprime_le_dist_lowerbound (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] (h : ¬ Subsingleton C) :
  ∀ d ∈ {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}, (Code.dist' C).toNat ≤ d := by
  intro d hd
  rcases hd with ⟨u, hu, v, hv, hne, hle⟩
  have hdist : (Code.dist' C).toNat ≤ hammingDist u v :=
    code_toNat_distprime_le_pairDist (n:=n) (R:=R) (C:=C) hu hv hne
  exact le_trans hdist hle

theorem code_toNat_dist_prime_le_dist (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] : (Code.dist' C).toNat ≤ Code.dist C := by
  classical
  by_cases hC : Subsingleton C
  · -- Subsingleton case: show the defining set for Code.dist is empty
    have hSempty : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
      ext d; constructor
      · intro hd
        rcases hd with ⟨u, hu, v, hv, hne, _⟩
        -- In a subsingleton, u = v
        have : (⟨u, hu⟩ : C) = ⟨v, hv⟩ := Subsingleton.elim _ _
        have : u = v := by simpa using congrArg Subtype.val this
        exact (hne this).elim
      · intro hd; simpa using hd
    -- Using the definitions, both sides reduce to 0
    have hdist : Code.dist C = 0 := by simpa [Code.dist, hSempty]
    have hdist' : (Code.dist' C).toNat = 0 := by
      -- There are no distinct pairs in C, so the `min` is `⊤`, whose `toNat` is 0
      have hnoPairs : (((@Finset.univ (C × C) _).filter (fun p : C × C => p.1 ≠ p.2))) = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro p hp
        have : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
        exact this (Subsingleton.elim _ _)
      simpa [Code.dist', hnoPairs]
    simpa [hdist, hdist']
  · -- Nontrivial case: use the lower-bound axiom and apply le_csInf
    have hlower := code_toNat_distprime_le_dist_lowerbound (n := n) (R := R) (C := C) hC
    -- Produce a witness that the set is nonempty from a distinct pair in C
    have hpair := code_pairs_nonempty_of_not_subsingleton (n := n) (R := R) (C := C) hC
    have hnonempty : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}.Nonempty := by
      rcases hpair with ⟨p, hp⟩
      refine ⟨hammingDist (p.1 : n → R) (p.2 : n → R), ?_⟩
      refine ⟨p.1, (p.1).property, p.2, (p.2).property, ?_, le_rfl⟩
      -- Extract p.1 ≠ p.2 from membership in the filtered finset and transfer to coercions
      have : p ∈ ((@Finset.univ (C × C) _).filter (fun q : C × C => q.1 ≠ q.2)) := hp
      have hpne_sub : p.1 ≠ p.2 := by
        have := Finset.mem_filter.mp this
        exact this.2
      -- Turn inequality on subtypes into inequality on underlying terms
      exact fun h => hpne_sub (Subtype.ext (by simpa using h))
    -- Now apply le_csInf with the lower-bound property
    refine le_csInf hnonempty ?_
    intro d hd
    exact hlower d hd

theorem code_dist_prime_eq_dist (n : Type*) [Fintype n] (R : Type*) [DecidableEq R]
(C : Set (n → R)) [Fintype C] : (Code.dist' C).toNat = Code.dist C := by
  refine le_antisymm ?h₁ ?h₂
  · exact code_toNat_dist_prime_le_dist n R C
  · exact code_dist_le_toNat_dist_prime n R C

theorem finrank_le_card_of_injective_restrict (F : Type*) [CommRing F] [StrongRankCondition F]
(ι : Type*) [Fintype ι]
(LC : LinearCode ι F)
(S : Finset ι)
(h_inj : Function.Injective (fun (c : LC) => fun i : S => (c : ι → F) i)) :
  LinearCode.dim LC ≤ S.card := by
  classical
  -- Define the restriction linear map φ : LC →ₗ[F] (S → F)
  let φ : LC →ₗ[F] (S → F) :=
    {
      toFun := fun c => fun i : S => (c : ι → F) i,
      map_add' := by
        intro c d
        funext i
        rfl,
      map_smul' := by
        intro a c
        funext i
        rfl
    }
  -- φ is injective by the hypothesis on the underlying function
  have hφ_inj : Function.Injective φ := by
    simpa [φ] using h_inj
  -- Use StrongRankCondition to compare finranks via an injective linear map
  have hdim_le : Module.finrank F LC ≤ Module.finrank F (S → F) :=
    LinearMap.finrank_le_finrank_of_injective (f := φ) hφ_inj
  -- Compute finrank of (S → F)
  have hfinrank_pi : Module.finrank F (S → F) = Fintype.card S := by
    simpa using (Module.finrank_pi (R := F) (ι := S))
  -- Conclude, rewriting dim and finrank of (S → F)
  simpa [LinearCode.dim, hfinrank_pi, Fintype.card_coe] using hdim_le

theorem linearcode_pair_dist_le_iff_norm_le (F : Type*) [CommRing F] [DecidableEq F]
(ι : Type*) [Fintype ι]
(LC : LinearCode ι F) (d : ℕ) :
  (∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d)
  ↔ (∃ w ∈ LC, w ≠ 0 ∧ hammingNorm w ≤ d) := by
  classical
  constructor
  · rintro ⟨u, hu, v, hv, hne, hd⟩
    refine ⟨u - v, ?_, ?_, ?_⟩
    · simpa using (LC.sub_mem hu hv)
    · intro h
      exact hne (sub_eq_zero.mp h)
    · simpa [LinearCode.hammingDist_eq_wt_sub, Code.wt_eq_hammingNorm] using hd
  · rintro ⟨w, hw, hne, hnorm⟩
    refine ⟨w, hw, 0, by simpa using (LC.zero_mem), ?_, ?_⟩
    · exact hne
    · simpa [LinearCode.hammingDist_eq_wt_sub, Code.wt_eq_hammingNorm, sub_zero] using hnorm

theorem linearcode_dist_eq_distFromHammingNorm (F : Type*) [CommRing F] [DecidableEq F]
(ι : Type*) [Fintype ι]
(LC : LinearCode ι F) :
  Code.dist LC.carrier = LinearCode.disFromHammingNorm LC := by
  classical
  -- Show the defining sets inside the sInf are equal pointwise in d
  have hset :
      {d : ℕ | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d}
        = {d : ℕ | ∃ w ∈ LC, w ≠ (0 : _) ∧ hammingNorm w ≤ d} := by
    ext d
    -- Use the provided equivalence for each d
    simpa using (linearcode_pair_dist_le_iff_norm_le F ι LC d)
  -- Now unfold both sides and rewrite by hset
  simpa [Code.dist, LinearCode.disFromHammingNorm, hset]

theorem projection_eq_iff_eq_on {ι F : Type*} [DecidableEq ι]
(S : Finset ι) (f g : ι → F) :
  projection S f = projection S g ↔ ∀ i ∈ S, f i = g i := by
  constructor
  · intro h i hi
    have := congrArg (fun hfun => hfun ⟨i, hi⟩) h
    simpa [projection] using this
  · intro h
    funext j
    rcases j with ⟨i, hi⟩
    simpa [projection] using h i hi

theorem linearcode_projection_injective_minDist (F : Type*) [CommRing F] [DecidableEq F]
(ι : Type*) [Fintype ι]
(LC : LinearCode ι F)
(S : Finset ι)
(hS : S.card = Fintype.card ι - (Code.minDist (LC : Set (ι → F)) - 1))
(c d : LC) :
  projection S (c : ι → F) = projection S (d : ι → F) → c = d := by
  intro hproj
  classical
  -- Work by contradiction
  by_contra hcd
  -- Underlying functions u,v
  set u : ι → F := (c : ι → F) with hu
  set v : ι → F := (d : ι → F) with hv
  -- From equality of projections, u and v agree on S
  have heq_on_S : ∀ i ∈ S, u i = v i := by
    exact (projection_eq_iff_eq_on (ι := ι) (F := F) S u v).1 (by simpa [hu, hv] using hproj)
  -- Define the set of coordinates where u and v differ
  let D : Finset ι := Finset.univ.filter (fun i => u i ≠ v i)
  -- D is contained in the complement of S
  have hD_subset : D ⊆ Sᶜ := by
    intro i hiD
    have hiNe : u i ≠ v i := (Finset.mem_filter.mp hiD).2
    -- If i ∈ S, then u i = v i by heq_on_S, contradiction
    refine Finset.mem_compl.mpr ?_
    intro hiS
    exact hiNe (heq_on_S i hiS)
  -- Hence |D| ≤ |Sᶜ|
  have hcard_le : D.card ≤ (Sᶜ).card := Finset.card_mono hD_subset
  -- Identify |D| with the Hamming distance
  have hD_card : D.card = hammingDist u v := by
    simp [D, hammingDist]
  have hdist_le : hammingDist u v ≤ (Sᶜ).card := by
    simpa [hD_card] using hcard_le
  -- Bound |Sᶜ| by minDist - 1 using the given hypothesis on |S|
  have hScard_le : (Sᶜ).card ≤ Code.minDist (LC : Set (ι → F)) - 1 := by
    -- (Sᶜ).card = |ι| - |S| = |ι| - (|ι| - (minDist - 1)) = min |ι| (minDist - 1) ≤ minDist - 1
    calc
      (Sᶜ).card = Fintype.card ι - S.card := by simpa using (Finset.card_compl (s := S))
      _ = Fintype.card ι - (Fintype.card ι - (Code.minDist (LC : Set (ι → F)) - 1)) := by simpa [hS]
      _ = Nat.min (Fintype.card ι) (Code.minDist (LC : Set (ι → F)) - 1) := by
        simpa using (Nat.sub_sub_eq_min (Fintype.card ι) (Code.minDist (LC : Set (ι → F)) - 1))
      _ ≤ Code.minDist (LC : Set (ι → F)) - 1 := Nat.min_le_right _ _
  have hdist_ub : hammingDist u v ≤ Code.minDist (LC : Set (ι → F)) - 1 :=
    le_trans hdist_le hScard_le
  -- Also, min distance is ≤ pairwise distance for distinct codewords
  have hneq_uv : u ≠ v := by
    intro hEq
    apply hcd
    apply Subtype.ext
    simpa [hu, hv] using hEq
  have hmin_le : Code.minDist (LC : Set (ι → F)) ≤ hammingDist u v := by
    -- use the provided axiom
    have huC : u ∈ (LC : Set (ι → F)) := by simpa [hu] using c.property
    have hvC : v ∈ (LC : Set (ι → F)) := by simpa [hv] using d.property
    simpa [hu, hv] using
      (code_minDist_le_pairDist (ι := ι) (F := F) (C := (LC : Set (ι → F))) (u := u) (v := v) huC hvC hneq_uv)
  -- Now split on whether minDist = 0
  by_cases h0 : Code.minDist (LC : Set (ι → F)) = 0
  · -- then the upper bound forces hamming distance to be 0, contradicting u ≠ v
    have hd_le_zero : hammingDist u v ≤ 0 := by simpa [h0] using hdist_ub
    have hd0 : hammingDist u v = 0 := Nat.le_zero.mp hd_le_zero
    -- From distance zero, there are no differing coordinates, hence u=v
    have hDempty : D = (∅ : Finset ι) := by
      apply Finset.card_eq_zero.mp
      simpa [hD_card, hd0]
    have : u = v := by
      funext i
      by_contra hne
      have hi_univ : i ∈ Finset.univ := by simp
      have hiD : i ∈ D := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨hi_univ, hne⟩
      -- but D is empty
      simpa [hDempty] using hiD
    exact hneq_uv this
  · -- minDist > 0, so d ≤ m-1 implies d < m
    have hpos : 0 < Code.minDist (LC : Set (ι → F)) := Nat.pos_of_ne_zero h0
    have hdist_lt : hammingDist u v < Code.minDist (LC : Set (ι → F)) :=
      Nat.lt_of_le_sub_one hpos hdist_ub
    have : Code.minDist (LC : Set (ι → F)) < Code.minDist (LC : Set (ι → F)) :=
      Nat.lt_of_le_of_lt hmin_le hdist_lt
    exact (lt_irrefl _ : ¬ _ < _) this

theorem singletonBound_main (F : Type*) [CommRing F] [DecidableEq F] [StrongRankCondition F]
(ι : Type*) [Fintype ι]
(LC : LinearCode ι F) :
  LinearCode.dim LC ≤ LinearCode.length LC - Code.minDist (LC : Set (ι → F)) + 1 := by
  classical
  -- Define k := |ι| - (minDist - 1)
  set k := Fintype.card ι - (Code.minDist (LC : Set (ι → F)) - 1) with hk
  -- Bound k ≤ |ι|
  have hk_le_card : k ≤ Fintype.card ι := by
    simpa [k] using Nat.sub_le (Fintype.card ι) (Code.minDist (LC : Set (ι → F)) - 1)
  -- Choose S ⊆ univ with |S| = k
  obtain ⟨S, hSsubset, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := k)
      (by simpa [Finset.card_univ] using hk_le_card)
  have hS : S.card = Fintype.card ι - (Code.minDist (LC : Set (ι → F)) - 1) := by
    simpa [k] using hScard
  -- Injectivity of restriction map to S via min distance
  have h_inj : Function.Injective (fun (c : LC) => fun i : S => (c : ι → F) i) := by
    intro c d hcd
    exact (linearcode_projection_injective_minDist F ι LC S hS c d) (by simpa using hcd)
  -- Dimension bound from injective restriction
  have hdim_le_S : LinearCode.dim LC ≤ S.card :=
    finrank_le_card_of_injective_restrict F ι LC S h_inj
  -- Replace S.card with k
  have hdim_le_k : LinearCode.dim LC ≤ k := by simpa [k, hS] using hdim_le_S
  -- Compare k with |ι| - minDist + 1
  have hk_le_rhs : k ≤ Fintype.card ι - Code.minDist (LC : Set (ι → F)) + 1 := by
    -- Split on the value of minDist
    cases h : Code.minDist (LC : Set (ι → F)) with
    | zero =>
        -- k = |ι|, so |ι| ≤ |ι| + 1
        simpa [k, h] using Nat.le_succ (Fintype.card ι)
    | succ m =>
        -- k = |ι| - m, and RHS is |ι| - (m+1) + 1 = (|ι| - m) - 1 + 1
        have hk' : k = Fintype.card ι - m := by simpa [k, h, Nat.succ_sub_one]
        -- Set x := |ι| - m
        set x := Fintype.card ι - m with hx
        -- a general inequality: x ≤ (x - 1) + 1
        have hx_le : x ≤ (x - 1) + 1 := by
          cases x with
          | zero => simp
          | succ t => simp
        -- rewrite RHS using sub_sub
        simpa [hx, hk', h, Nat.sub_sub] using hx_le
  -- Combine and rewrite length = |ι|
  have : LinearCode.dim LC ≤ Fintype.card ι - Code.minDist (LC : Set (ι → F)) + 1 :=
    le_trans hdim_le_k hk_le_rhs
  simpa [LinearCode.length] using this
