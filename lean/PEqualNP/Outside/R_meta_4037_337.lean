import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix vertex 0. The two readers copy a wire on the low slice and supply opposite
-- constants on the high slice. The same sixteen gates must compute both slices.
-- On a pivotal row a monotone core must copy false at the OR reader.
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_4037_337
    (orFirst : let run := fun (gs : List Gate) (w : List Bool) => (Circuit.mk gs 0).wires w
    let base := fun (t : ℕ) => (false :: (List.range 9).map t.testBit) ++ [true]
    let target := fun (t : ℕ) (b : Bool) => (b && (t &&& 25 != 0)) ||
      (List.range 9).any (fun k => t.testBit k && (t &&& (([34, 68, 136, 256, 64, 128, 256, 16, 32] : List ℕ).getD k 0) != 0))
    ∀ (p m : List Gate) (s : Circuit) (i j : ℕ),
    FanInTwo ⟨p ++ m ++ s.gates, 0⟩ → p.length + m.length + s.size = 16 →
    (i < 11 → j < 11 → i = 0 ∨ j = 10 ∨ i = j) →
    (Monotone2 ⟨p ++ m ++ s.gates, 0⟩ → (i = 0 ∨ 11 ≤ i) ∧
      ∀ r : Fin 512, target r.val false = false → target r.val true = true →
        let w := run p (base r.val)
        w.getD i false = false) →
    ¬ ∀ (r : Fin 512) (b : Bool),
      let t := r.val
      let w := run p (base t)
      let v := run m (w ++ [if b then true else w.getD i false])
      s.eval (v ++ [if b then false else v.getD j false]) =
        target t b)
    (andFirst : let run := fun (gs : List Gate) (w : List Bool) => (Circuit.mk gs 0).wires w
    let base := fun (t : ℕ) => (false :: (List.range 9).map t.testBit) ++ [true]
    let target := fun (t : ℕ) (b : Bool) => (b && (t &&& 25 != 0)) ||
      (List.range 9).any (fun k => t.testBit k && (t &&& (([34, 68, 136, 256, 64, 128, 256, 16, 32] : List ℕ).getD k 0) != 0))
    ∀ (p m : List Gate) (s : Circuit) (i j : ℕ),
    FanInTwo ⟨p ++ m ++ s.gates, 0⟩ → p.length + m.length + s.size = 16 →
    (i < 11 → j < 11 → j = 0 ∨ i = 10 ∨ i = j) →
    (Monotone2 ⟨p ++ m ++ s.gates, 0⟩ → (j = 0 ∨ 11 ≤ j) ∧
      ∀ r : Fin 512, target r.val false = false → target r.val true = true →
        let w := run p (base r.val)
        (run m (w ++ [w.getD i false])).getD j false = false) →
    ¬ ∀ (r : Fin 512) (b : Bool),
      let t := r.val
      let w := run p (base t)
      let v := run m (w ++ [if b then false else w.getD i false])
      s.eval (v ++ [if b then true else v.getD j false]) =
        target t b)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → ¬∃ (x5 : Fin x1.gates.length) (x6 : Fin x1.gates.length), x5 ≠ x6 ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∈ (x1.gates.get x5).inputs ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (10 : ℕ) ∈ (x1.gates.get x6).inputs ∧ ∀ x7 ∈ [((0 : ℕ), x5), ((10 : ℕ), x6)], ∀ (x9 : Fin x1.gates.length), ((x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x9).inputs.head? = Option.some x7.1 → x9 = x7.2) ∧ ((x1.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.1 ∈ (x1.gates.get x9).inputs → x9 = x7.2) := by
  let run := fun (gs : List Gate) (w : List Bool) => (Circuit.mk gs 0).wires w
  let val := fun (g : Gate) (w : List Bool) => g.op.eval (g.inputs.map (w.getD · false))
  let row := fun (r : Fin 512) (b : Bool) => (b :: (List.range 9).map r.val.testBit) ++ [!b]
  let rhs := fun (r : Fin 512) (b : Bool) => (b && (r.val &&& 25 != 0)) ||
    (List.range 9).any (fun k => r.val.testBit k && (r.val &&&
      (([34,68,136,256,64,128,256,16,32] : List ℕ).getD k 0) != 0))
  let tail := fun (g : Gate) (k : ℕ) =>
    ((g.inputs.erase k).head?).getD k
  have run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      run (g :: gs) w = run gs (w ++ [val g w]) := rfl
  have run_append (p q : List Gate) (w : List Bool) :
      run (p ++ q) w = run q (run p w) := by
    exact List.foldl_append
  have extends' (gs : List Gate) (w : List Bool) : ∃ a, run gs w = w ++ a := by
    induction gs generalizing w with
    | nil => exact ⟨[], (List.append_nil _).symm⟩
    | cons g gs ih =>
      obtain ⟨a,ha⟩ := ih (w ++ [val g w])
      exact ⟨val g w :: a, (run_cons g gs w).trans (ha.trans (List.append_assoc ..))⟩
  have len (r : Fin 512) (b : Bool) : (row r b).length = 11 := by simp [row]
  have atZero (r : Fin 512) (b : Bool) (a : List Bool) :
      (row r b ++ a).getD 0 false = b := rfl
  have atTen (r : Fin 512) (b : Bool) (a : List Bool) :
      (row r b ++ a).getD 10 false = !b := rfl
  have agree (r : Fin 512) (b : Bool) (a : List Bool) (i : ℕ) (hz : i ≠ 0) (ht : i ≠ 10) :
      (row r b ++ a).getD i false = (row r false ++ a).getD i false := by
    by_cases h : i < 11
    · interval_cases i <;> first | rfl | contradiction
    · rw [List.getD_append_right _ _ _ _ (by rw [len]; omega),
          List.getD_append_right _ _ _ _ (by rw [len]; omega), len, len]
  let uses := fun (g : Gate) (k : ℕ) =>
    (g.op = GateOp.not ∧ g.inputs.head? = some k) ∨ (g.op ≠ GateOp.not ∧ k ∈ g.inputs)
  have evNot (w : List Bool) : GateOp.not.eval w = !(w.headD false) := rfl
  have evAnd (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have evOr (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  have gate_eq (g : Gate) (r : Fin 512) (b : Bool) (a : List Bool)
      (hz : ¬uses g 0) (ht : ¬uses g 10) :
      val g (row r b ++ a) = val g (row r false ++ a) := by
    by_cases hn : g.op = .not
    · cases he : g.inputs with
      | nil => simp only [val,he,List.map_nil]
      | cons i l =>
        have hi (k : ℕ) (h : ¬uses g k) : i ≠ k := by
          rintro rfl
          exact h (Or.inl ⟨hn,by rw [he]; rfl⟩)
        simpa only [val,hn,he,List.map_cons,evNot,List.headD_cons] using
          congrArg Bool.not (agree r b a i (hi 0 hz) (hi 10 ht))
    · apply congrArg g.op.eval
      apply List.map_congr_left
      intro i h
      exact agree r b a i (fun e => hz (Or.inr ⟨hn,e ▸ h⟩)) (fun e => ht (Or.inr ⟨hn,e ▸ h⟩))
  have segment (p : List Gate) (ok : ∀ g ∈ p, ¬uses g 0 ∧ ¬uses g 10)
      (r : Fin 512) (b : Bool) (a : List Bool) :
      ∃ d, run p (row r b ++ a) = row r b ++ d ∧
           run p (row r false ++ a) = row r false ++ d := by
    induction p generalizing a with
    | nil => exact ⟨a,rfl,rfl⟩
    | cons g gs ih =>
      obtain ⟨hz,ht⟩ := ok g (List.mem_cons_self ..)
      obtain ⟨d,h₁,h₂⟩ := ih (fun v hv => ok v (List.mem_cons_of_mem g hv))
        (a ++ [val g (row r false ++ a)])
      refine ⟨d,?_,?_⟩
      · rw [run_cons,gate_eq g r b a hz ht,List.append_assoc,h₁]
      · rw [run_cons,List.append_assoc,h₂]
  have zeroGet (r : Fin 512) (b : Bool) (a : List Bool) : (row r b ++ a)[0]?.getD false = b := rfl
  have tenGet (r : Fin 512) (b : Bool) (a : List Bool) : (row r b ++ a)[10]?.getD false = !b := rfl
  have reader (g : Gate) (pos : Bool) (hk : (if pos then 0 else 10) ∈ g.inputs)
      (hop : g.op = (if pos then GateOp.or else GateOp.and))
      (arity : g.inputs.length ≤ 2) (r : Fin 512) (b : Bool) (a : List Bool) :
      val g (row r b ++ a) = (if b then pos else
        (row r false ++ a).getD (tail g (if pos then 0 else 10)) false) := by
    generalize h : g.inputs = l at *
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k,l⟩⟩⟩
    · simp at hk
    · simp only [List.mem_singleton] at hk
      subst i
      cases pos <;> cases b <;> simp [val,tail,h,hop,evAnd,evOr,zeroGet,tenGet]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with hi | hj
      · subst i
        cases pos <;> cases b <;> simp [val,tail,h,hop,evAnd,evOr,zeroGet,tenGet]
      · subst j
        cases pos <;> cases b <;>
          simp [val,tail,h,hop,evAnd,evOr,zeroGet,tenGet,List.erase_cons] <;>
          split <;> simp_all
    · simp at arity
  intro C hf hn computes
  rintro ⟨o,a,ne,oo,oi,aa,ai,unique⟩
  let x := fun (r : Fin 512) (b : Bool) (i : Fin 10) => if i.val = 0 then b else r.val.testBit (i.val-1)
  have input (r : Fin 512) (b : Bool) : List.ofFn (x r b) ++ [!x r b 0] = row r b := by rfl
  have targets : ∀ (r : Fin 512) (b : Bool),
      (let y := x r b
       y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
       y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 4 && y 9 ||
       y 5 && y 7 || y 7 && y 9 || y 9 && y 6 || y 6 && y 8 || y 8 && y 5) = rhs r b := by
    dsimp only [x,rhs]
    decide +kernel
  have calcRow (r : Fin 512) (b : Bool) : C.eval (row r b) = rhs r b := by
    rw [←input,computes]
    exact targets r b
  have hout : C.output ≠ 0 ∧ C.output ≠ 10 := by
    have same (i : ℕ) (hi : i = 0 ∨ i = 10) (hh : C.output = i) : False := by
      obtain ⟨u,hu⟩ := extends' C.gates (row 0 false)
      obtain ⟨v,hv⟩ := extends' C.gates (row 3 false)
      have eqval : (run C.gates (row 0 false)).getD C.output false =
          (run C.gates (row 3 false)).getD C.output false := by
        rcases hi with rfl | rfl <;> rw [hu,hv,hh] <;> rfl
      change C.eval (row 0 false) = C.eval (row 3 false) at eqval
      rw [calcRow,calcRow] at eqval
      exact Bool.noConfusion eqval
    exact ⟨same 0 (.inl rfl),same 10 (.inr rfl)⟩
  have named (j : Fin C.gates.length) :
      (uses (C.gates.get j) 0 → j = o) ∧ (uses (C.gates.get j) 10 → j = a) := by
    have h0 := unique (0,o) (List.mem_cons_self ..) j
    have h10 := unique (10,a) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) j
    exact ⟨fun h => h.elim (fun v => h0.1 v.1 v.2) (fun v => h0.2 v.1 v.2),
      fun h => h.elim (fun v => h10.1 v.1 v.2) (fun v => h10.2 v.1 v.2)⟩
  have twoCuts (i j : Fin C.gates.length) (lt : i < j) :
      ∃ p m s : List Gate, C.gates = p ++ C.gates.get i :: (m ++ C.gates.get j :: s) ∧
        p.length = i.val ∧ p.length + 1 + m.length = j.val := by
    let n := j.val - (i.val + 1)
    let rest := C.gates.drop (i.val + 1)
    have hi := i.isLt
    have hj := j.isLt
    have hij : i.val < j.val := lt
    have nlt : n < rest.length := by simp only [n,rest,List.length_drop]; omega
    have idx : i.val + 1 + n = j.val := by dsimp [n]; omega
    have hfirst : C.gates = C.gates.take i.val ++ C.gates.get i :: rest := by
      exact (List.take_append_drop i.val C.gates).symm.trans
        (congrArg (List.append (C.gates.take i.val)) (List.drop_eq_getElem_cons hi))
    have hsecond : rest = rest.take n ++ rest[n] :: rest.drop (n+1) := by
      conv_lhs => rw [←List.take_append_drop n rest, List.drop_eq_getElem_cons nlt]
    have hget : rest[n] = C.gates.get j := by
      simp only [rest,List.getElem_drop,idx,List.get_eq_getElem]
    refine ⟨C.gates.take i.val,rest.take n,rest.drop (n+1),?_,?_,?_⟩
    · calc
        C.gates = C.gates.take i.val ++ C.gates.get i :: rest := hfirst
        _ = _ := by conv_lhs => rw [hsecond,hget]
    · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
    · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi),
        Nat.min_eq_left (Nat.le_of_lt nlt),idx]
  have cleanPart (pre gs post : List Gate) (he : C.gates = pre ++ (gs ++ post))
      (away : ∀ k < gs.length, pre.length+k ≠ o.val ∧ pre.length+k ≠ a.val) :
      ∀ g ∈ gs, ¬uses g 0 ∧ ¬uses g 10 := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hg
    have hh : pre.length+k < C.gates.length := by rw [he]; simp; omega
    let z : Fin C.gates.length := ⟨pre.length+k,hh⟩
    have eqg : C.gates.get z = gs[k] := by
      change C.gates[pre.length+k] = gs[k]
      simp only [he,List.getElem_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,
        List.getElem_append_left hk]
    have un := named z
    rw [eqg] at un
    exact ⟨fun h => (away k hk).1 (congrArg Fin.val (un.1 h)),
      fun h => (away k hk).2 (congrArg Fin.val (un.2 h))⟩
  have pivot : ∀ (i j : Fin 11), i.val ≠ 0 → j.val ≠ 10 → i ≠ j →
      ∃ r : Fin 512, (row r false).getD i.val false = true ∧
        (row r false).getD j.val false = false ∧ rhs r false ≠ rhs r true := by
    dsimp only [row,rhs]
    decide +kernel
  have positive : ∀ i : Fin 11, i.val ≠ 0 →
      ∃ r : Fin 512, (row r false).getD i.val false = true ∧
        rhs r false = false ∧ rhs r true = true := by
    dsimp only [row,rhs]
    decide +kernel
  let rel := List.Forall₂ (fun x y : Bool => x ≤ y)
  have project (w z : List Bool) (h : rel w z) (i : ℕ) : w.getD i false ≤ z.getD i false := by
    by_cases hi : i < w.length
    · have hj : i < z.length := h.length_eq ▸ hi
      simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj,List.get_eq_getElem] using
        h.get hi hj
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Bool.false_le _
  have extend (w z : List Bool) (x y : Bool) (h : rel w z) (xy : x ≤ y) :
      rel (w ++ [x]) (z ++ [y]) := List.rel_append h (.cons xy .nil)
  have runMono (gs : List Gate) (clean : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (w z : List Bool) (h : rel w z) : rel (run gs w) (run gs z) := by
    induction gs generalizing w z with
    | nil => exact h
    | cons g gs ih =>
      rw [run_cons,run_cons]
      apply ih (fun t ht => clean t (List.mem_cons_of_mem g ht))
      apply extend w z _ _ h
      apply Bool.le_iff_imp.mpr
      rcases clean g (List.mem_cons_self ..) with he | he
      · simp only [val,he,evAnd,List.all_eq_true,List.mem_map,forall_exists_index,
          and_imp,forall_apply_eq_imp_iff₂,id_eq]
        intro all i hi
        exact Bool.le_iff_imp.mp (project w z h i) (all i hi)
      · simp only [val,he,evOr,List.any_eq_true,List.mem_map,exists_exists_and_eq_and,id_eq]
        rintro ⟨i,hi,hit⟩
        exact ⟨i,hi,Bool.le_iff_imp.mp (project w z h i) hit⟩
  have normal (i j : Fin C.gates.length) (pos : Bool) (lt : i < j)
      (order : (i=o ∧ j=a) ∨ (i=a ∧ j=o))
      (opI : (C.gates.get i).op = if pos then GateOp.or else GateOp.and)
      (inI : (if pos then 0 else 10) ∈ (C.gates.get i).inputs)
      (opJ : (C.gates.get j).op = if !pos then GateOp.or else GateOp.and)
      (inJ : (if !pos then 0 else 10) ∈ (C.gates.get j).inputs) : False := by
    obtain ⟨p,m,s,split,pi,mj⟩ := twoCuts i j lt
    let g := C.gates.get i
    let h := C.gates.get j
    change C.gates = p ++ g :: (m ++ h :: s) at split
    have hfan (v : Gate) (hv : v ∈ p ++ m ++ s) := hf v (by
      rw [split]; simpa only [List.mem_append,List.mem_cons] using
        (show v ∈ p ∨ v = g ∨ v ∈ m ∨ v = h ∨ v ∈ s from by
          rcases List.mem_append.mp hv with hpm | hs
          · rcases List.mem_append.mp hpm with hp | hm
            · exact Or.inl hp
            · exact Or.inr (.inr (.inl hm))
          · exact Or.inr (.inr (.inr (.inr hs)))))
    have budget : p.length + m.length + s.length = 16 := by
      change C.gates.length = 18 at hn
      rw [split] at hn
      simp only [List.length_append,List.length_cons] at hn
      omega
    have ord : (i.val=o.val ∧ j.val=a.val) ∨ (i.val=a.val ∧ j.val=o.val) :=
      order.imp (fun h => ⟨congrArg Fin.val h.1,congrArg Fin.val h.2⟩)
        (fun h => ⟨congrArg Fin.val h.1,congrArg Fin.val h.2⟩)
    have safeP := cleanPart [] p (g :: (m ++ h :: s)) (by simpa only [List.nil_append] using split)
      (by intro k hk; simp only [List.length_nil,Nat.zero_add]; rcases ord with e | e <;> constructor <;> omega)
    have safeM := cleanPart (p ++ [g]) m (h :: s) (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
      (by intro k hk; simp only [List.length_append,List.length_cons,List.length_nil]; rcases ord with e | e <;> constructor <;> omega)
    have safeS := cleanPart (p ++ g :: (m ++ [h])) s [] (by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using split)
      (by intro k hk; simp only [List.length_append,List.length_cons,List.length_nil]; rcases ord with e | e <;> constructor <;> omega)
    let u := tail g (if pos then 0 else 10)
    let v := tail h (if !pos then 0 else 10)
    let suffix : Circuit := ⟨s,C.output⟩
    have hit (r : Fin 512) (b : Bool) :
        (let w := run p (row r false)
         let z := run m (w ++ [if b then pos else w.getD u false])
         suffix.eval (z ++ [if b then !pos else z.getD v false])) = rhs r b := by
      obtain ⟨d,dp,dp'⟩ := segment p safeP r b []
      simp only [List.append_nil] at dp dp'
      let c := if b then pos else (row r false ++ d).getD u false
      have vg : val g (row r b ++ d) = c :=
        reader g pos inI opI (hf g (List.get_mem ..)).2 r b d
      obtain ⟨e,em,em'⟩ := segment m safeM r b (d ++ [c])
      let f := if b then !pos else (row r false ++ e).getD v false
      have vh : val h (row r b ++ e) = f :=
        reader h (!pos) inJ opJ (hf h (List.get_mem ..)).2 r b e
      obtain ⟨k,ks,ks'⟩ := segment s safeS r b (e ++ [f])
      have orig := calcRow r b
      change (run C.gates (row r b)).getD C.output false = _ at orig
      rw [split,run_append,dp,run_cons,vg,List.append_assoc,run_append,em,
        run_cons,vh,List.append_assoc,ks] at orig
      dsimp only
      rw [dp']
      change (run s ((run m ((row r false ++ d) ++ [c])) ++
        [if b then !pos else (run m ((row r false ++ d) ++ [c])).getD v false])).getD C.output false = _
      rw [List.append_assoc,em']
      change (run s ((row r false ++ e) ++ [f])).getD C.output false = _
      rw [List.append_assoc,ks',←agree r b k C.output hout.1 hout.2]
      exact orig
    have raw (hu : u < 11) (hv : v < 11)
        (wrong : ∃ r : Fin 512, (row r false).getD u false = pos ∧
          (row r false).getD v false = !pos ∧ rhs r false ≠ rhs r true) : False := by
      obtain ⟨r,huv,hvv,changeOut⟩ := wrong
      let w := run p (row r false)
      let z := run m (w ++ [pos])
      obtain ⟨t,ht⟩ := extends' p (row r false)
      have wu : w.getD u false = pos := by
        rw [show w = row r false ++ t from ht,List.getD_append _ _ _ _ (by rw [len]; exact hu),huv]
      obtain ⟨q,hq⟩ := extends' m (w ++ [pos])
      have zv : z.getD v false = !pos := by
        change (run m (w ++ [pos])).getD v false = _
        rw [hq,show w = row r false ++ t from ht,List.append_assoc,List.append_assoc,
          List.getD_append _ _ _ _ (by rw [len]; exact hv),hvv]
      have low := hit r false
      have high := hit r true
      change suffix.eval ((run m (w ++ [w.getD u false])) ++
        [(run m (w ++ [w.getD u false])).getD v false]) = _ at low
      rw [wu] at low
      change suffix.eval (z ++ [z.getD v false]) = _ at low
      rw [zv] at low
      exact changeOut (low.symm.trans high)
    have monoRow (hmono : Monotone2 ⟨p ++ m ++ s, 0⟩) (r : Fin 512)
        (low : rhs r false = false) (high : rhs r true = true) :
        (let w := run p (row r false)
         let z := run m (w ++ [w.getD u false])
         if pos then w.getD u false else z.getD v false) = false := by
      let w := run p (row r false)
      let z₀ := run m (w ++ [w.getD u false])
      let z₁ := run m (w ++ [pos])
      change (if pos then w.getD u false else z₀.getD v false) = false
      apply Bool.eq_false_iff.mpr
      intro on
      have bounds : pos ≤ w.getD u false ∧ (!pos) ≤ z₀.getD v false := by
        cases pos
        · exact ⟨Bool.false_le _,le_of_eq on.symm⟩
        · exact ⟨le_of_eq on.symm,Bool.false_le _⟩
      have allOp (g : Gate) (hg : g ∈ p ++ m ++ s) : g.op = .and ∨ g.op = .or :=
        (hmono g hg).1
      have refw : rel w w := List.forall₂_iff_get.mpr ⟨rfl,fun _ _ _ => le_rfl⟩
      have cmpM : rel z₁ z₀ := runMono m (fun g hg =>
        allOp g (List.mem_append_left _ (List.mem_append_right _ hg))) _ _ (extend _ _ _ _ refw bounds.1)
      have cmpS := runMono s (fun g hg => allOp g (List.mem_append_right _ hg)) _ _
        (extend _ _ _ _ cmpM bounds.2)
      have out := project _ _ cmpS C.output
      change suffix.eval (z₁ ++ [!pos]) ≤ suffix.eval (z₀ ++ [z₀.getD v false]) at out
      have hh : suffix.eval (z₁ ++ [!pos]) = rhs r true := hit r true
      have hl : suffix.eval (z₀ ++ [z₀.getD v false]) = rhs r false := hit r false
      rw [hh,hl,high,low] at out
      exact Bool.noConfusion (Bool.eq_true_of_true_le out)
    have monoIndex (hmono : Monotone2 ⟨p ++ m ++ s, 0⟩) :
        (if pos then u else v) = 0 ∨ 11 ≤ (if pos then u else v) := by
      by_contra! small
      obtain ⟨r,lit,low,high⟩ := positive ⟨_,small.2⟩ small.1
      have lit' : (row r false).getD (if pos then u else v) false = true := lit
      have off := monoRow hmono r low high
      obtain ⟨d,hd⟩ := extends' p (row r false)
      rw [hd] at off
      cases pos
      · obtain ⟨e,he⟩ := extends' m ((row r false ++ d) ++ [(row r false ++ d).getD u false])
        change (run m ((row r false ++ d) ++ [(row r false ++ d).getD u false])).getD v false = false at off
        change (row r false).getD v false = true at lit'
        rw [he,List.append_assoc,List.append_assoc] at off
        rw [List.getD_append _ _ _ _ (by rw [len]; exact small.2),lit'] at off
        contradiction
      · change (row r false).getD u false = true at lit'
        change ((row r false ++ d).getD u false) = false at off
        rw [List.getD_append _ _ _ _ (by rw [len]; exact small.2),lit'] at off
        contradiction
    cases pos
    · apply andFirst p m suffix u v hfan budget _ (fun hm => ⟨monoIndex hm,monoRow hm⟩) hit
      intro hu hv
      by_contra! hbad
      apply raw hu hv
      obtain ⟨r,hv',hu',hd⟩ := pivot ⟨v,hv⟩ ⟨u,hu⟩ hbad.1 hbad.2.1
        (fun eq => hbad.2.2 (congrArg Fin.val eq).symm)
      exact ⟨r,hu',hv',hd⟩
    · apply orFirst p m suffix u v hfan budget _ (fun hm => ⟨monoIndex hm,monoRow hm⟩) hit
      intro hu hv
      by_contra! hbad
      apply raw hu hv
      obtain ⟨r,hu',hv',hd⟩ := pivot ⟨u,hu⟩ ⟨v,hv⟩ hbad.1 hbad.2.1
        (fun eq => hbad.2.2 (congrArg Fin.val eq))
      exact ⟨r,hu',hv',hd⟩
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact normal o a true lt (.inl ⟨rfl,rfl⟩) oo oi aa ai
  · exact normal a o false gt (.inr ⟨rfl,rfl⟩) aa ai oo oi
