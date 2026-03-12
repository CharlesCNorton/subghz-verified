(******************************************************************************)
(*                                                                            *)
(*                       Thresholded OOK Run Semantics                        *)
(*                                                                            *)
(*     Formalizes thresholded OOK traces from raw IQ window energies.         *)
(*     Proves burst detection, run flattening, onset/offset soundness,        *)
(*     and normalized pulse-gap classification across timing scales.          *)
(*                                                                            *)
(*     "The true logic of this world is the calculus of probabilities."       *)
(*     - James Clerk Maxwell, 1850                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 11, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)


From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Definition Window := bool.
Definition Trace := list Window.

Fixpoint count_active (xs : Trace) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => (if x then 1 else 0) + count_active xs'
  end.

Fixpoint take (n : nat) (xs : Trace) : Trace :=
  match n, xs with
  | O, _ => []
  | S n', [] => []
  | S n', x :: xs' => x :: take n' xs'
  end.

Fixpoint drop (n : nat) (xs : Trace) : Trace :=
  match n, xs with
  | O, _ => xs
  | S n', [] => []
  | S n', _ :: xs' => drop n' xs'
  end.

Definition window_active_count (span : nat) (xs : Trace) : nat :=
  count_active (take span xs).

Definition dense_window (span min_active : nat) (xs : Trace) : bool :=
  Nat.leb min_active (window_active_count span xs).

Fixpoint first_dense_window (span min_active : nat) (xs : Trace) : option nat :=
  match xs with
  | [] =>
      if dense_window span min_active [] then Some 0 else None
  | _ :: xs' =>
      if dense_window span min_active xs then
        Some 0
      else
        match first_dense_window span min_active xs' with
        | Some idx => Some (S idx)
        | None => None
        end
  end.

Definition has_dense_window (span min_active : nat) (xs : Trace) : bool :=
  match first_dense_window span min_active xs with
  | Some _ => true
  | None => false
  end.

Fixpoint first_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      if x then
        Some 0
      else
        match first_true xs' with
        | Some idx => Some (S idx)
        | None => None
        end
  end.

Fixpoint last_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      match last_true xs' with
      | Some idx => Some (S idx)
      | None => if x then Some 0 else None
      end
  end.

Lemma dense_window_true :
  forall span min_active xs,
    dense_window span min_active xs = true ->
    min_active <= window_active_count span xs.
Proof.
  intros span min_active xs H.
  unfold dense_window in H.
  apply Nat.leb_le.
  exact H.
Qed.

Lemma take_app_prefix :
  forall n xs ys,
    n <= length xs ->
    take n (xs ++ ys) = take n xs.
Proof.
  induction n as [|n IH]; intros xs ys Hlen.
  - reflexivity.
  - destruct xs as [|x xs']; simpl in *.
    + lia.
    + f_equal.
      apply IH.
      lia.
Qed.

Lemma take_drop :
  forall n xs,
    take n xs ++ drop n xs = xs.
Proof.
  induction n as [|n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Theorem first_dense_window_sound :
  forall span min_active xs idx,
    first_dense_window span min_active xs = Some idx ->
    idx <= length xs /\
    min_active <= window_active_count span (drop idx xs).
Proof.
  induction xs as [|x xs IH]; intros idx Hscan; simpl in Hscan.
  - destruct (dense_window span min_active []) eqn:Hdense.
    + inversion Hscan; subst.
      split.
      * lia.
      * apply dense_window_true.
        exact Hdense.
    + discriminate.
  - destruct (dense_window span min_active (x :: xs)) eqn:Hdense.
    + inversion Hscan; subst.
      split.
      * lia.
      * apply dense_window_true.
        exact Hdense.
    + destruct (first_dense_window span min_active xs) eqn:Htail.
      * inversion Hscan; subst.
        specialize (IH n eq_refl) as [Hidx Hcount].
        split.
        -- simpl.
           lia.
        -- simpl.
           exact Hcount.
      * discriminate.
Qed.

Theorem first_dense_window_complete_from_suffix :
  forall prefix suffix span min_active,
    min_active <= window_active_count span suffix ->
    exists idx,
      first_dense_window span min_active (prefix ++ suffix) = Some idx.
Proof.
  induction prefix as [|x prefix IH]; intros suffix span min_active Hcount.
  - destruct suffix as [|w ws].
    + assert (Hzero : window_active_count span [] = 0).
      {
        unfold window_active_count.
        destruct span; reflexivity.
      }
      rewrite Hzero in Hcount.
      destruct min_active as [|min_active'].
      * simpl.
        eexists.
        reflexivity.
      * exfalso.
        lia.
    + simpl.
      assert (Hdense : dense_window span min_active (w :: ws) = true).
      {
        unfold dense_window.
        apply Nat.leb_le.
        exact Hcount.
      }
      rewrite Hdense.
      eexists.
      reflexivity.
  - simpl.
    destruct (dense_window span min_active (x :: prefix ++ suffix))
      eqn:Hdense_now.
    + eexists.
      reflexivity.
    + destruct (IH suffix span min_active Hcount) as [idx Hidx].
      rewrite Hidx.
      eexists.
      reflexivity.
Qed.

Corollary has_dense_window_complete_from_suffix :
  forall prefix suffix span min_active,
    min_active <= window_active_count span suffix ->
    has_dense_window span min_active (prefix ++ suffix) = true.
Proof.
  intros prefix suffix span min_active Hcount.
  destruct (first_dense_window_complete_from_suffix prefix suffix span min_active Hcount)
    as [idx Hidx].
  unfold has_dense_window.
  rewrite Hidx.
  reflexivity.
Qed.

Theorem first_dense_window_complete :
  forall prefix block suffix span min_active,
    span <= length block ->
    min_active <= window_active_count span block ->
    exists idx,
      first_dense_window span min_active (prefix ++ block ++ suffix) = Some idx.
Proof.
  induction prefix as [|x prefix IH]; intros block suffix span min_active Hspan Hdense.
  - destruct (block ++ suffix) as [|w ws] eqn:Htrace.
    + assert (Hnil : block = [] /\ suffix = []).
      { apply app_eq_nil in Htrace.
        exact Htrace. }
      destruct Hnil as [Hblock Hsuffix].
      subst block suffix.
      simpl in Hspan.
      assert (span = 0).
      { lia. }
      subst span.
      unfold window_active_count in Hdense.
      simpl in Hdense.
      assert (min_active = 0).
      { lia. }
      subst min_active.
      simpl.
      eexists.
      reflexivity.
    + simpl.
      assert (Hhead : dense_window span min_active (block ++ suffix) = true).
      {
        unfold dense_window, window_active_count.
        rewrite take_app_prefix with (ys := suffix).
        - apply Nat.leb_le.
          exact Hdense.
        - exact Hspan.
      }
      rewrite <- Htrace.
      rewrite Hhead.
      eexists.
      reflexivity.
  - simpl.
    destruct (dense_window span min_active ((x :: prefix) ++ block ++ suffix))
      eqn:Hdense_now.
    + change (dense_window span min_active (x :: prefix ++ block ++ suffix) = true)
        in Hdense_now.
      rewrite Hdense_now.
      eexists.
      reflexivity.
    + change (dense_window span min_active (x :: prefix ++ block ++ suffix) = false)
        in Hdense_now.
      destruct (IH block suffix span min_active Hspan Hdense) as [idx Hidx].
      rewrite Hdense_now.
      rewrite Hidx.
      eexists.
      reflexivity.
Qed.

Corollary has_dense_window_complete :
  forall prefix block suffix span min_active,
    span <= length block ->
    min_active <= window_active_count span block ->
    has_dense_window span min_active (prefix ++ block ++ suffix) = true.
Proof.
  intros prefix block suffix span min_active Hspan Hdense.
  destruct (first_dense_window_complete prefix block suffix span min_active Hspan Hdense)
    as [idx Hidx].
  unfold has_dense_window.
  rewrite Hidx.
  reflexivity.
Qed.

Lemma first_true_sound_match :
  forall xs,
    match first_true xs with
    | Some idx =>
        idx < length xs /\
        nth idx xs false = true /\
        (forall j, j < idx -> nth j xs false = false)
    | None => True
    end.
Proof.
  induction xs as [|x xs IH]; simpl.
  - trivial.
  - destruct x.
    + split.
      * simpl.
        lia.
      * split.
        -- reflexivity.
        -- intros j Hj.
           assert (False) by lia.
           contradiction.
    + destruct (first_true xs) as [idx|] eqn:Hfirst; simpl.
      * destruct IH as [Hlt [Hnth Hprefix]].
        repeat split.
        -- simpl.
           lia.
        -- simpl.
           exact Hnth.
        -- intros j Hj.
           destruct j.
           ++ reflexivity.
           ++ simpl.
              apply Hprefix.
              lia.
      * trivial.
Qed.

Theorem first_true_sound :
  forall xs idx,
    first_true xs = Some idx ->
    idx < length xs /\
    nth idx xs false = true /\
    (forall j, j < idx -> nth j xs false = false).
Proof.
  intros xs idx H.
  pose proof (first_true_sound_match xs) as Hsound.
  rewrite H in Hsound.
  exact Hsound.
Qed.

Theorem last_true_none_all_false :
  forall xs,
    last_true xs = None ->
    forall j, j < length xs -> nth j xs false = false.
Proof.
  induction xs as [|x xs IH]; intros Hnone j Hj.
  - destruct j; reflexivity.
  - simpl in Hnone.
    destruct (last_true xs) eqn:Hlast.
    + discriminate.
    + destruct x.
      * discriminate.
      * destruct j.
        -- reflexivity.
        -- simpl.
           simpl in Hj.
           assert (Hj' : j < length xs).
           { lia. }
           apply IH.
           ++ exact Hnone.
           ++ exact Hj'.
Qed.

Lemma last_true_sound_match :
  forall xs,
    match last_true xs with
    | Some idx =>
        idx < length xs /\
        nth idx xs false = true /\
        (forall j, idx < j -> j < length xs -> nth j xs false = false)
    | None => True
    end.
Proof.
  induction xs as [|x xs IH]; simpl.
  - trivial.
  - destruct (last_true xs) eqn:Hlast; simpl.
    + destruct IH as [Hlt [Hnth Hsuffix]].
      repeat split.
      * simpl.
        lia.
      * simpl.
        exact Hnth.
      * intros j Hij Hjlen.
        destruct j.
        -- lia.
        -- simpl.
           apply Hsuffix.
           ++ lia.
           ++ lia.
    + destruct x.
      * split.
        -- simpl.
           lia.
        -- split.
           ++ reflexivity.
           ++ intros j Hij Hjlen.
              destruct j.
              ** lia.
              ** simpl.
                 simpl in Hjlen.
                 assert (Hjlen' : j < length xs).
                 { lia. }
                 eapply last_true_none_all_false.
                 --- exact Hlast.
                 --- exact Hjlen'.
      * trivial.
Qed.

Theorem last_true_sound :
  forall xs idx,
    last_true xs = Some idx ->
    idx < length xs /\
    nth idx xs false = true /\
    (forall j, idx < j -> j < length xs -> nth j xs false = false).
Proof.
  intros xs idx H.
  pose proof (last_true_sound_match xs) as Hsound.
  rewrite H in Hsound.
  exact Hsound.
Qed.

Definition Run := (Window * nat)%type.
Definition Runs := list Run.

Fixpoint repeat_window (b : Window) (n : nat) : Trace :=
  match n with
  | O => []
  | S n' => b :: repeat_window b n'
  end.

Lemma repeat_window_snoc :
  forall b n,
    repeat_window b n ++ [b] = repeat_window b (S n).
Proof.
  intros b n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_shift :
  forall b n xs,
    b :: repeat_window b n ++ xs = repeat_window b n ++ b :: xs.
Proof.
  intros b n xs.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_length :
  forall b n,
    length (repeat_window b n) = n.
Proof.
  intros b n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_app :
  forall b n m,
    repeat_window b (n + m) = repeat_window b n ++ repeat_window b m.
Proof.
  intros b n m.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Fixpoint flatten_runs (rs : Runs) : Trace :=
  match rs with
  | [] => []
  | (b, n) :: rs' => repeat_window b n ++ flatten_runs rs'
  end.

Fixpoint runs_of_trace (current : Window) (len : nat) (xs : Trace) : Runs :=
  match xs with
  | [] => [(current, len)]
  | x :: xs' =>
      if Bool.eqb x current then
        runs_of_trace current (S len) xs'
      else
        (current, len) :: runs_of_trace x 1 xs'
  end.

Definition rle_trace (xs : Trace) : Runs :=
  match xs with
  | [] => []
  | x :: xs' => runs_of_trace x 1 xs'
  end.

Fixpoint runs_positive (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (_, O) :: _ => false
  | (_, S _) :: rs' => runs_positive rs'
  end.

Fixpoint runs_alternate_from (current : Window) (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (b, _) :: rs' =>
      negb (Bool.eqb b current) && runs_alternate_from b rs'
  end.

Definition runs_alternating (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (b, _) :: rs' => runs_alternate_from b rs'
  end.

Fixpoint active_run_lengths (rs : Runs) : list nat :=
  match rs with
  | [] => []
  | (b, n) :: rs' =>
      if b then n :: active_run_lengths rs' else active_run_lengths rs'
  end.

Fixpoint inactive_run_lengths (rs : Runs) : list nat :=
  match rs with
  | [] => []
  | (b, n) :: rs' =>
      if b then inactive_run_lengths rs' else n :: inactive_run_lengths rs'
  end.

Fixpoint strip_leading_false_runs (rs : Runs) : Runs :=
  match rs with
  | (false, _) :: rs' => strip_leading_false_runs rs'
  | _ => rs
  end.

Definition strip_trailing_false_runs (rs : Runs) : Runs :=
  rev (strip_leading_false_runs (rev rs)).

Definition canonical_runs (rs : Runs) : Runs :=
  strip_trailing_false_runs (strip_leading_false_runs rs).

Lemma active_run_lengths_strip_leading_false_runs :
  forall rs,
    active_run_lengths (strip_leading_false_runs rs) = active_run_lengths rs.
Proof.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + exact IH.
Qed.

Lemma active_run_lengths_app :
  forall rs1 rs2,
    active_run_lengths (rs1 ++ rs2) =
      active_run_lengths rs1 ++ active_run_lengths rs2.
Proof.
  induction rs1 as [|(b, n) rs1 IH]; intros rs2; simpl.
  - reflexivity.
  - destruct b; simpl.
    + rewrite (IH rs2).
      reflexivity.
    + exact (IH rs2).
Qed.

Lemma active_run_lengths_rev :
  forall rs,
    active_run_lengths (rev rs) = rev (active_run_lengths rs).
Proof.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - rewrite active_run_lengths_app.
    rewrite IH.
    destruct b; simpl.
    + reflexivity.
    + rewrite app_nil_r.
      reflexivity.
Qed.

Lemma active_run_lengths_strip_trailing_false_runs :
  forall rs,
    active_run_lengths (strip_trailing_false_runs rs) = active_run_lengths rs.
Proof.
  intro rs.
  unfold strip_trailing_false_runs.
  rewrite active_run_lengths_rev.
  rewrite active_run_lengths_strip_leading_false_runs.
  rewrite active_run_lengths_rev.
  rewrite rev_involutive.
  reflexivity.
Qed.

Corollary active_run_lengths_canonical_runs :
  forall rs,
    active_run_lengths (canonical_runs rs) = active_run_lengths rs.
Proof.
  intros rs.
  unfold canonical_runs.
  rewrite active_run_lengths_strip_trailing_false_runs.
  apply active_run_lengths_strip_leading_false_runs.
Qed.

Definition scale_run (factor : nat) (r : Run) : Run :=
  let '(b, n) := r in
  (b, factor * n).

Definition scale_runs (factor : nat) (rs : Runs) : Runs :=
  map (scale_run factor) rs.

Lemma scale_runs_length :
  forall factor rs,
    length (scale_runs factor rs) = length rs.
Proof.
  intros factor rs.
  unfold scale_runs.
  rewrite length_map.
  reflexivity.
Qed.

Lemma scale_runs_app :
  forall factor rs1 rs2,
    scale_runs factor (rs1 ++ rs2) =
      scale_runs factor rs1 ++ scale_runs factor rs2.
Proof.
  intros factor rs1 rs2.
  unfold scale_runs.
  rewrite map_app.
  reflexivity.
Qed.

Lemma scale_runs_rev :
  forall factor rs,
    scale_runs factor (rev rs) = rev (scale_runs factor rs).
Proof.
  intros factor rs.
  unfold scale_runs.
  rewrite map_rev.
  reflexivity.
Qed.

Lemma active_run_lengths_scale :
  forall factor rs,
    active_run_lengths (scale_runs factor rs) =
      map (Nat.mul factor) (active_run_lengths rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + rewrite IH.
      reflexivity.
    + exact IH.
Qed.

Lemma inactive_run_lengths_scale :
  forall factor rs,
    inactive_run_lengths (scale_runs factor rs) =
      map (Nat.mul factor) (inactive_run_lengths rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + exact IH.
    + rewrite IH.
      reflexivity.
Qed.

Theorem runs_positive_scale :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_positive (scale_runs factor rs) = true.
Proof.
  intros factor rs Hfactor Hpos.
  destruct factor as [|factor'].
  { lia. }
  induction rs as [|(b, n) rs IH]; simpl in *.
  - reflexivity.
  - destruct n.
    + discriminate.
    + destruct b; simpl.
      * apply IH.
        exact Hpos.
      * apply IH.
        exact Hpos.
Qed.

Theorem runs_alternating_scale :
  forall factor rs,
    runs_alternating rs = true ->
    runs_alternating (scale_runs factor rs) = true.
Proof.
  intros factor rs.
  unfold runs_alternating.
  destruct rs as [|(b, n) rs']; simpl.
  - reflexivity.
  - revert b.
    induction rs' as [|(b', n') rs'' IH]; intros b Halt; simpl in *.
    + reflexivity.
    + apply andb_true_iff in Halt as [Hneq Hrest].
      apply andb_true_iff.
      split.
      * exact Hneq.
      * apply IH.
        exact Hrest.
Qed.

Lemma flatten_runs_of_trace :
  forall current len xs,
    0 < len ->
    flatten_runs (runs_of_trace current len xs) = repeat_window current len ++ xs.
Proof.
  intros current len xs.
  revert current len.
  induction xs as [|x xs IH]; intros current len Hlen.
  - simpl.
    reflexivity.
  - simpl.
    destruct (Bool.eqb x current) eqn:Heq.
    + destruct x, current; simpl in Heq; try discriminate.
      * rewrite IH.
        -- simpl.
           apply repeat_window_shift.
        -- lia.
      * rewrite IH.
        -- simpl.
           apply repeat_window_shift.
        -- lia.
    + simpl.
      rewrite IH.
      * simpl.
        reflexivity.
      * lia.
Qed.

Lemma runs_of_trace_extend_same :
  forall current len extra xs,
    runs_of_trace current len (repeat_window current extra ++ xs) =
      runs_of_trace current (len + extra) xs.
Proof.
  intros current len extra xs.
  revert current len xs.
  induction extra as [|extra IH]; intros current len xs; simpl.
  - replace (len + 0) with len by lia.
    reflexivity.
  - simpl.
    simpl.
    rewrite (IH current (S len) xs).
    destruct (Bool.eqb current current) eqn:Heq.
    + replace (S len + extra) with (len + S extra) by lia.
      reflexivity.
    + apply Bool.eqb_false_iff in Heq.
      contradiction Heq.
      reflexivity.
Qed.

Theorem flatten_rle_trace :
  forall xs,
    flatten_runs (rle_trace xs) = xs.
Proof.
  intros xs.
  destruct xs as [|x xs'].
  - reflexivity.
  - unfold rle_trace.
    rewrite flatten_runs_of_trace.
    + simpl.
      reflexivity.
    + lia.
Qed.

Lemma runs_of_trace_flatten_runs :
  forall current len rs,
    0 < len ->
    runs_positive rs = true ->
    runs_alternate_from current rs = true ->
    runs_of_trace current len (flatten_runs rs) = (current, len) :: rs.
Proof.
  intros current len rs Hlen.
  revert current len Hlen.
  induction rs as [|(b, n) rs' IH]; intros current len Hlen Hpos Halt; simpl in *.
  - reflexivity.
  - destruct n as [|n']; [discriminate|].
    apply andb_true_iff in Halt as [Hneq Hrest].
    apply Bool.negb_true_iff in Hneq.
    apply Bool.eqb_false_iff in Hneq.
    simpl.
    assert (Hneqb : Bool.eqb b current = false).
    { apply Bool.eqb_false_iff.
      exact Hneq. }
    rewrite Hneqb.
    rewrite runs_of_trace_extend_same.
    f_equal.
    apply IH.
    * lia.
    * exact Hpos.
    * exact Hrest.
Qed.

Theorem rle_trace_flatten_runs_well_formed :
  forall rs,
    runs_positive rs = true ->
    runs_alternating rs = true ->
    rle_trace (flatten_runs rs) = rs.
Proof.
  intros rs Hpos Halt.
  destruct rs as [|(b, n) rs']; simpl in *.
  - reflexivity.
  - destruct n as [|n']; [discriminate|].
    simpl.
    rewrite runs_of_trace_extend_same.
    apply runs_of_trace_flatten_runs.
    + lia.
    + exact Hpos.
    + exact Halt.
Qed.

Lemma runs_of_trace_positive :
  forall current len xs,
    0 < len ->
    runs_positive (runs_of_trace current len xs) = true.
Proof.
  intros current len xs.
  revert current len.
  induction xs as [|x xs IH]; intros current len Hlen.
  - simpl.
    destruct len; [lia|reflexivity].
  - simpl.
    destruct (Bool.eqb x current) eqn:Heq.
    + apply IH.
      lia.
    + simpl.
      destruct len; [lia|].
      simpl.
      apply IH.
      lia.
Qed.

Theorem rle_trace_positive :
  forall xs,
    runs_positive (rle_trace xs) = true.
Proof.
  intros xs.
  destruct xs as [|x xs'].
  - reflexivity.
  - unfold rle_trace.
    apply runs_of_trace_positive.
    lia.
Qed.

Fixpoint min_list_from (current : nat) (xs : list nat) : nat :=
  match xs with
  | [] => current
  | x :: xs' => min_list_from (Nat.min current x) xs'
  end.

Definition min_list_default (default : nat) (xs : list nat) : nat :=
  match xs with
  | [] => default
  | x :: xs' => min_list_from x xs'
  end.

Inductive PulseClass :=
| MarkShort
| MarkLong
| GapShort
| GapLong
| GapBreak.

Inductive CoarsePulseClass :=
| CoarseMarkShort
| CoarseMarkLong
| CoarseGap
| CoarseGapBreak.

Definition classify_run_with_base (base : nat) (r : Run) : PulseClass :=
  let '(b, n) := r in
  if b then
    if Nat.ltb n (2 * base) then MarkShort else MarkLong
  else
    if Nat.ltb n (2 * base) then GapShort
    else if Nat.ltb n (10 * base) then GapLong
    else GapBreak.

Definition classify_runs_with_base (base : nat) (rs : Runs) : list PulseClass :=
  map (classify_run_with_base base) rs.

Definition coarsen_pulse_class (cls : PulseClass) : CoarsePulseClass :=
  match cls with
  | MarkShort => CoarseMarkShort
  | MarkLong => CoarseMarkLong
  | GapShort => CoarseGap
  | GapLong => CoarseGap
  | GapBreak => CoarseGapBreak
  end.

Definition coarse_pulse_classes (xs : list PulseClass) : list CoarsePulseClass :=
  map coarsen_pulse_class xs.

Definition pulse_base_from_runs (rs : Runs) : nat :=
  min_list_default 1 (active_run_lengths rs).

Definition normalized_pulse_classes (rs : Runs) : list PulseClass :=
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Definition canonical_pulse_base_from_runs (rs : Runs) : nat :=
  pulse_base_from_runs (canonical_runs rs).

Definition canonical_normalized_pulse_classes (rs : Runs) : list PulseClass :=
  normalized_pulse_classes (canonical_runs rs).

Inductive FrameToken :=
| FrameBitZero
| FrameBitOne
| FrameBreak
| FrameUnknown.

Fixpoint frame_tokens_from_classes (xs : list PulseClass) : list FrameToken :=
  match xs with
  | [] => []
  | GapBreak :: xs' => FrameBreak :: frame_tokens_from_classes xs'
  | MarkShort :: GapLong :: xs' =>
      FrameBitZero :: frame_tokens_from_classes xs'
  | MarkLong :: GapShort :: xs' =>
      FrameBitOne :: frame_tokens_from_classes xs'
  | _ :: xs' => FrameUnknown :: frame_tokens_from_classes xs'
  end.

Fixpoint first_frame_bits_from_tokens_aux
    (started : bool)
    (xs : list FrameToken)
    : list bool :=
  match xs with
  | [] => []
  | FrameBreak :: xs' =>
      if started then [] else first_frame_bits_from_tokens_aux false xs'
  | FrameBitZero :: xs' =>
      false :: first_frame_bits_from_tokens_aux true xs'
  | FrameBitOne :: xs' =>
      true :: first_frame_bits_from_tokens_aux true xs'
  | FrameUnknown :: xs' =>
      if started then [] else first_frame_bits_from_tokens_aux false xs'
  end.

Definition first_frame_bits_from_tokens (xs : list FrameToken) : list bool :=
  first_frame_bits_from_tokens_aux false xs.

Definition token_noise_prefix (xs : list FrameToken) : Prop :=
  Forall (fun tok => tok = FrameBreak \/ tok = FrameUnknown) xs.

Lemma first_frame_bits_from_tokens_aux_true_app_break :
  forall xs ys,
    first_frame_bits_from_tokens_aux true (xs ++ FrameBreak :: ys) =
      first_frame_bits_from_tokens_aux true xs.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - reflexivity.
  - destruct x; simpl.
    + rewrite IH.
      reflexivity.
    + rewrite IH.
      reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Theorem first_frame_bits_from_tokens_prefix_noise_invariant :
  forall prefix xs,
    token_noise_prefix prefix ->
    first_frame_bits_from_tokens (prefix ++ xs) =
      first_frame_bits_from_tokens xs.
Proof.
  intros prefix xs Hnoise.
  induction Hnoise; simpl.
  - reflexivity.
  - destruct H as [Hbreak | Hunknown]; subst; simpl; exact IHHnoise.
Qed.

Theorem first_frame_bits_from_tokens_suffix_break_invariant :
  forall xs,
    first_frame_bits_from_tokens (xs ++ [FrameBreak]) =
      first_frame_bits_from_tokens xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - unfold first_frame_bits_from_tokens in *.
    simpl.
    destruct x; simpl.
    + f_equal.
      apply first_frame_bits_from_tokens_aux_true_app_break.
    + f_equal.
      apply first_frame_bits_from_tokens_aux_true_app_break.
    + exact IH.
    + exact IH.
Qed.

Definition frame_bits_from_classes (xs : list PulseClass) : list bool :=
  first_frame_bits_from_tokens (frame_tokens_from_classes xs).

Fixpoint classes_of_bits (xs : list bool) : list PulseClass :=
  match xs with
  | [] => [GapBreak]
  | false :: xs' => MarkShort :: GapLong :: classes_of_bits xs'
  | true :: xs' => MarkLong :: GapShort :: classes_of_bits xs'
  end.

Lemma frame_tokens_from_classes_of_bits :
  forall xs,
    frame_tokens_from_classes (classes_of_bits xs) =
      map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak].
Proof.
  induction xs as [|b xs IH]; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma frame_tokens_from_classes_of_bits_app :
  forall xs suffix,
    frame_tokens_from_classes (classes_of_bits xs ++ suffix) =
      map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++
      frame_tokens_from_classes (GapBreak :: suffix).
Proof.
  induction xs as [|b xs IH]; intro suffix; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma first_frame_bits_from_bit_tokens_aux_true :
  forall xs,
    first_frame_bits_from_tokens_aux true
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak]) = xs.
Proof.
  induction xs as [|b xs IH]; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma first_frame_bits_from_bit_tokens :
  forall xs,
    first_frame_bits_from_tokens
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak]) = xs.
Proof.
  intro xs.
  unfold first_frame_bits_from_tokens.
  simpl.
  destruct xs as [|b xs].
  - reflexivity.
  - destruct b; simpl; f_equal; apply first_frame_bits_from_bit_tokens_aux_true.
Qed.

Lemma first_frame_bits_from_bit_tokens_then_break_suffix :
  forall xs ys,
    first_frame_bits_from_tokens_aux true
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ FrameBreak :: ys) = xs.
Proof.
  induction xs as [|b xs IH]; intro ys; simpl.
  - reflexivity.
  - destruct b; simpl; f_equal; apply IH.
Qed.

Theorem frame_bits_from_classes_of_bits :
  forall xs,
    frame_bits_from_classes (classes_of_bits xs) = xs.
Proof.
  intro xs.
  unfold frame_bits_from_classes.
  rewrite frame_tokens_from_classes_of_bits.
  apply first_frame_bits_from_bit_tokens.
Qed.

Theorem frame_bits_from_classes_of_bits_with_suffix :
  forall xs suffix,
    xs <> [] ->
    frame_bits_from_classes (classes_of_bits xs ++ suffix) = xs.
Proof.
  intros xs suffix Hnonempty.
  destruct xs as [|b xs].
  - contradiction.
  - unfold frame_bits_from_classes.
    rewrite frame_tokens_from_classes_of_bits_app.
    unfold first_frame_bits_from_tokens.
    simpl.
    destruct b; simpl; f_equal;
      apply first_frame_bits_from_bit_tokens_then_break_suffix.
Qed.

Definition packet_alias_classes (xs ys : list PulseClass) : Prop :=
  frame_bits_from_classes xs = frame_bits_from_classes ys.

Theorem classes_of_bits_suffix_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet_alias_classes
      (classes_of_bits bits ++ suffix1)
      (classes_of_bits bits ++ suffix2).
Proof.
  intros bits suffix1 suffix2 Hbits.
  unfold packet_alias_classes.
  rewrite (frame_bits_from_classes_of_bits_with_suffix bits suffix1 Hbits).
  rewrite (frame_bits_from_classes_of_bits_with_suffix bits suffix2 Hbits).
  reflexivity.
Qed.

Theorem packet_alias_classes_noninjective :
  forall bits,
    bits <> [] ->
    exists xs ys,
      xs <> ys /\
      frame_bits_from_classes xs = bits /\
      frame_bits_from_classes ys = bits.
Proof.
  intros bits Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - split.
    + apply frame_bits_from_classes_of_bits_with_suffix.
      exact Hbits.
    + apply frame_bits_from_classes_of_bits_with_suffix.
      exact Hbits.
Qed.

Theorem packet_alias_classes_infinite_tail_family :
  forall bits n1 n2,
    bits <> [] ->
    packet_alias_classes
      (classes_of_bits bits ++ repeat MarkShort n1)
      (classes_of_bits bits ++ repeat MarkShort n2).
Proof.
  intros bits n1 n2 Hbits.
  apply classes_of_bits_suffix_alias.
  exact Hbits.
Qed.

Theorem packet_alias_classes_tail_family_distinct :
  forall bits n1 n2,
    bits <> [] ->
    n1 <> n2 ->
    classes_of_bits bits ++ repeat MarkShort n1 <>
      classes_of_bits bits ++ repeat MarkShort n2.
Proof.
  intros bits n1 n2 Hbits Hneq Heq.
  assert (Hlen :
    length (classes_of_bits bits ++ repeat MarkShort n1) =
    length (classes_of_bits bits ++ repeat MarkShort n2)).
  { rewrite Heq. reflexivity. }
  repeat rewrite length_app in Hlen.
  repeat rewrite repeat_length in Hlen.
  lia.
Qed.

Corollary frame_bits_from_classes_token_suffix_break_invariant :
  forall xs,
    first_frame_bits_from_tokens (frame_tokens_from_classes xs ++ [FrameBreak]) =
      frame_bits_from_classes xs.
Proof.
  intro xs.
  unfold frame_bits_from_classes.
  apply first_frame_bits_from_tokens_suffix_break_invariant.
Qed.

Definition canonical_frame_bits_from_runs (rs : Runs) : list bool :=
  frame_bits_from_classes (canonical_normalized_pulse_classes rs).

Fixpoint bits_to_nat_acc (acc : nat) (xs : list bool) : nat :=
  match xs with
  | [] => acc
  | x :: xs' =>
      bits_to_nat_acc (2 * acc + if x then 1 else 0) xs'
  end.

Definition bits_to_nat (xs : list bool) : nat :=
  bits_to_nat_acc 0 xs.

Definition canonical_frame_word_from_runs (rs : Runs) : nat :=
  bits_to_nat (canonical_frame_bits_from_runs rs).

Record Packet24 := {
  packet24_hi : nat;
  packet24_mid : nat;
  packet24_lo : nat
}.

Record BitFieldSpec := {
  field_offset : nat;
  field_width : nat
}.

Definition field_bits (spec : BitFieldSpec) (xs : list bool) : list bool :=
  take (field_width spec) (drop (field_offset spec) xs).

Definition field_value (spec : BitFieldSpec) (xs : list bool) : nat :=
  bits_to_nat (field_bits spec xs).

Definition packet24_hi_byte_field : BitFieldSpec :=
  {| field_offset := 0; field_width := 8 |}.

Definition packet24_mid_byte_field : BitFieldSpec :=
  {| field_offset := 8; field_width := 8 |}.

Definition packet24_hi16_field : BitFieldSpec :=
  {| field_offset := 0; field_width := 16 |}.

Definition packet24_lo_byte_field : BitFieldSpec :=
  {| field_offset := 16; field_width := 8 |}.

Definition packet24_prefix12_field : BitFieldSpec :=
  {| field_offset := 0; field_width := 12 |}.

Definition packet24_suffix12_field : BitFieldSpec :=
  {| field_offset := 12; field_width := 12 |}.

Definition packet24_nibble0_field : BitFieldSpec :=
  {| field_offset := 0; field_width := 4 |}.

Definition packet24_nibble1_field : BitFieldSpec :=
  {| field_offset := 4; field_width := 4 |}.

Definition packet24_nibble2_field : BitFieldSpec :=
  {| field_offset := 8; field_width := 4 |}.

Definition packet24_nibble3_field : BitFieldSpec :=
  {| field_offset := 12; field_width := 4 |}.

Definition packet24_nibble4_field : BitFieldSpec :=
  {| field_offset := 16; field_width := 4 |}.

Definition packet24_nibble5_field : BitFieldSpec :=
  {| field_offset := 20; field_width := 4 |}.

Definition packet24_from_bits (xs : list bool) : Packet24 :=
  {| packet24_hi := bits_to_nat (take 8 xs);
     packet24_mid := bits_to_nat (take 8 (drop 8 xs));
     packet24_lo := bits_to_nat (take 8 (drop 16 xs)) |}.

Record Packet24ByteView := {
  packet24_byte0 : nat;
  packet24_byte1 : nat;
  packet24_byte2 : nat
}.

Definition packet24_byte_view_from_bits (xs : list bool) : Packet24ByteView :=
  {| packet24_byte0 := field_value packet24_hi_byte_field xs;
     packet24_byte1 := field_value packet24_mid_byte_field xs;
     packet24_byte2 := field_value packet24_lo_byte_field xs |}.

Record Packet24NibbleView := {
  packet24_nibble0 : nat;
  packet24_nibble1 : nat;
  packet24_nibble2 : nat;
  packet24_nibble3 : nat;
  packet24_nibble4 : nat;
  packet24_nibble5 : nat
}.

Definition packet24_nibble_view_from_bits (xs : list bool) : Packet24NibbleView :=
  {| packet24_nibble0 := field_value packet24_nibble0_field xs;
     packet24_nibble1 := field_value packet24_nibble1_field xs;
     packet24_nibble2 := field_value packet24_nibble2_field xs;
     packet24_nibble3 := field_value packet24_nibble3_field xs;
     packet24_nibble4 := field_value packet24_nibble4_field xs;
     packet24_nibble5 := field_value packet24_nibble5_field xs |}.

Record Packet24FieldView := {
  packet24_fields_bytes : Packet24ByteView;
  packet24_fields_nibbles : Packet24NibbleView;
  packet24_fields_prefix12 : nat;
  packet24_fields_suffix12 : nat
}.

Definition packet24_field_view_from_bits (xs : list bool) : Packet24FieldView :=
  {| packet24_fields_bytes := packet24_byte_view_from_bits xs;
     packet24_fields_nibbles := packet24_nibble_view_from_bits xs;
     packet24_fields_prefix12 := field_value packet24_prefix12_field xs;
     packet24_fields_suffix12 := field_value packet24_suffix12_field xs |}.

Inductive PacketFieldRole :=
| PacketFieldPrefix
| PacketFieldPayload
| PacketFieldCounter
| PacketFieldFlag
| PacketFieldCheck
| PacketFieldBoundary
| PacketFieldReserved.

Definition packet_field_role_code (role : PacketFieldRole) : nat :=
  match role with
  | PacketFieldPrefix => 0
  | PacketFieldPayload => 1
  | PacketFieldCounter => 2
  | PacketFieldFlag => 3
  | PacketFieldCheck => 4
  | PacketFieldBoundary => 5
  | PacketFieldReserved => 6
  end.

Record PacketStructureFieldSpec := {
  packet_structure_role : PacketFieldRole;
  packet_structure_bits : BitFieldSpec
}.

Definition PacketStructureSpec := list PacketStructureFieldSpec.

Record PacketStructuredFieldValue := {
  structured_field_role : PacketFieldRole;
  structured_field_offset : nat;
  structured_field_width : nat;
  structured_field_value : nat
}.

Definition packet_structured_field_value_from_bits
    (spec : PacketStructureFieldSpec)
    (xs : list bool)
    : PacketStructuredFieldValue :=
  {| structured_field_role := packet_structure_role spec;
     structured_field_offset := field_offset (packet_structure_bits spec);
     structured_field_width := field_width (packet_structure_bits spec);
     structured_field_value := field_value (packet_structure_bits spec) xs |}.

Definition packet_structure_view_from_bits
    (spec : PacketStructureSpec)
    (xs : list bool)
    : list PacketStructuredFieldValue :=
  map (fun field_spec => packet_structured_field_value_from_bits field_spec xs) spec.

Definition packet_field_end (spec : BitFieldSpec) : nat :=
  field_offset spec + field_width spec.

Definition packet_field_spec_well_formed
    (spec : PacketStructureFieldSpec)
    : Prop :=
  0 < field_width (packet_structure_bits spec) /\
  packet_field_end (packet_structure_bits spec) <= 24.

Fixpoint packet_structure_spec_well_formed
    (spec : PacketStructureSpec)
    : Prop :=
  match spec with
  | [] => True
  | field_spec :: spec' =>
      packet_field_spec_well_formed field_spec /\
      packet_structure_spec_well_formed spec'
  end.

Definition packet24_byte_structure_spec : PacketStructureSpec :=
  [ {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_hi_byte_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_mid_byte_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_lo_byte_field |} ].

Definition packet24_nibble_structure_spec : PacketStructureSpec :=
  [ {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble0_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble1_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble2_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble3_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble4_field |};
    {| packet_structure_role := PacketFieldPayload;
       packet_structure_bits := packet24_nibble5_field |} ].

Definition packet24_hi16_lo8_structure_spec : PacketStructureSpec :=
  [ {| packet_structure_role := PacketFieldPrefix;
       packet_structure_bits := packet24_hi16_field |};
    {| packet_structure_role := PacketFieldCounter;
       packet_structure_bits := packet24_lo_byte_field |} ].

Definition packet24_prefix12_suffix12_structure_spec : PacketStructureSpec :=
  [ {| packet_structure_role := PacketFieldPrefix;
       packet_structure_bits := packet24_prefix12_field |};
    {| packet_structure_role := PacketFieldCounter;
       packet_structure_bits := packet24_suffix12_field |} ].

Record CounterSchema := {
  counter_schema_key : BitFieldSpec;
  counter_schema_value : BitFieldSpec
}.

Definition hi16_lo8_counter_schema : CounterSchema :=
  {| counter_schema_key := packet24_hi16_field;
     counter_schema_value := packet24_lo_byte_field |}.

Definition prefix12_suffix12_counter_schema : CounterSchema :=
  {| counter_schema_key := packet24_prefix12_field;
     counter_schema_value := packet24_suffix12_field |}.

Definition packet_structure_of_counter_schema
    (schema : CounterSchema)
    : PacketStructureSpec :=
  [ {| packet_structure_role := PacketFieldPrefix;
       packet_structure_bits := counter_schema_key schema |};
    {| packet_structure_role := PacketFieldCounter;
       packet_structure_bits := counter_schema_value schema |} ].

Record FieldCounterView := {
  field_counter_key : nat;
  field_counter_value : nat
}.

Definition field_counter_view_from_bits
    (schema : CounterSchema)
    (xs : list bool)
    : FieldCounterView :=
  {| field_counter_key := field_value (counter_schema_key schema) xs;
     field_counter_value := field_value (counter_schema_value schema) xs |}.

Definition hi16_lo8_counter_view_from_bits (xs : list bool) : FieldCounterView :=
  field_counter_view_from_bits hi16_lo8_counter_schema xs.

Definition prefix12_suffix12_counter_view_from_bits
    (xs : list bool)
    : FieldCounterView :=
  field_counter_view_from_bits prefix12_suffix12_counter_schema xs.

Definition field_counter_step (older newer : FieldCounterView) : Prop :=
  field_counter_key older = field_counter_key newer /\
  field_counter_value newer = S (field_counter_value older).

Definition field_counter_view_eqb
    (x y : FieldCounterView)
    : bool :=
  Nat.eqb (field_counter_key x) (field_counter_key y)
  &&
  Nat.eqb (field_counter_value x) (field_counter_value y).

Definition field_counter_stepb
    (older newer : FieldCounterView)
    : bool :=
  Nat.eqb (field_counter_key older) (field_counter_key newer)
  &&
  Nat.eqb (S (field_counter_value older)) (field_counter_value newer).

Fixpoint field_counter_step_sequence_from
    (older : FieldCounterView)
    (views : list FieldCounterView)
    : Prop :=
  match views with
  | [] => True
  | y :: views' =>
      field_counter_step older y /\
      field_counter_step_sequence_from y views'
  end.

Definition field_counter_step_sequence
    (views : list FieldCounterView)
    : Prop :=
  match views with
  | [] => True
  | x :: views' => field_counter_step_sequence_from x views'
  end.

Fixpoint field_counter_step_sequenceb_from
    (older : FieldCounterView)
    (views : list FieldCounterView)
    : bool :=
  match views with
  | [] => true
  | y :: views' =>
      field_counter_stepb older y
      &&
      field_counter_step_sequenceb_from y views'
  end.

Definition field_counter_step_sequenceb
    (views : list FieldCounterView)
    : bool :=
  match views with
  | [] => true
  | x :: views' => field_counter_step_sequenceb_from x views'
  end.

Definition counter_schema_fits_bits
    (schema : CounterSchema)
    (frames : list (list bool))
    : Prop :=
  field_counter_step_sequence
    (map (field_counter_view_from_bits schema) frames).

Definition counter_schema_fits_bitsb
    (schema : CounterSchema)
    (frames : list (list bool))
    : bool :=
  field_counter_step_sequenceb
    (map (field_counter_view_from_bits schema) frames).

Record CounterSchemaFitReport := {
  fit_report_hi16_lo8 : bool;
  fit_report_prefix12_suffix12 : bool
}.

Definition counter_schema_fit_report_from_bits
    (frames : list (list bool))
    : CounterSchemaFitReport :=
  {| fit_report_hi16_lo8 :=
       counter_schema_fits_bitsb hi16_lo8_counter_schema frames;
     fit_report_prefix12_suffix12 :=
       counter_schema_fits_bitsb prefix12_suffix12_counter_schema frames |}.

Definition counter_schema_classification_code_from_bits
    (frames : list (list bool))
    : nat :=
  let report := counter_schema_fit_report_from_bits frames in
  match fit_report_hi16_lo8 report, fit_report_prefix12_suffix12 report with
  | false, false => 0
  | true, false => 1
  | false, true => 2
  | true, true => 3
  end.

Definition prefix12_stronger_than_hi16_lo8b
    (frames : list (list bool))
    : bool :=
  negb (counter_schema_fits_bitsb hi16_lo8_counter_schema frames)
  &&
  counter_schema_fits_bitsb prefix12_suffix12_counter_schema frames.

Lemma field_counter_view_eqb_refl :
  forall view,
    field_counter_view_eqb view view = true.
Proof.
  intros [key value].
  unfold field_counter_view_eqb.
  simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  reflexivity.
Qed.

Theorem field_counter_stepb_sound :
  forall older newer,
    field_counter_stepb older newer = true ->
    field_counter_step older newer.
Proof.
  intros [older_key older_value] [newer_key newer_value] Hstep.
  unfold field_counter_stepb in Hstep.
  apply andb_true_iff in Hstep as [Hkey Hvalue].
  apply Nat.eqb_eq in Hkey.
  apply Nat.eqb_eq in Hvalue.
  split.
  - exact Hkey.
  - symmetry.
    exact Hvalue.
Qed.

Theorem field_counter_stepb_complete :
  forall older newer,
    field_counter_step older newer ->
    field_counter_stepb older newer = true.
Proof.
  intros [older_key older_value] [newer_key newer_value] [Hkey Hvalue].
  unfold field_counter_stepb.
  apply andb_true_iff.
  split.
  - apply Nat.eqb_eq.
    exact Hkey.
  - rewrite Hvalue.
    apply Nat.eqb_refl.
Qed.

Theorem field_counter_step_sequenceb_from_sound :
  forall older views,
    field_counter_step_sequenceb_from older views = true ->
    field_counter_step_sequence_from older views.
Proof.
  intros older views.
  revert older.
  induction views as [|view views IH]; intros older Hseq; simpl in *.
  - exact I.
  - apply andb_true_iff in Hseq as [Hstep Hrest].
    split.
    + apply field_counter_stepb_sound.
      exact Hstep.
    + apply IH.
      exact Hrest.
Qed.

Theorem field_counter_step_sequenceb_sound :
  forall views,
    field_counter_step_sequenceb views = true ->
    field_counter_step_sequence views.
Proof.
  intros [|view views] Hseq; simpl in *.
  - exact I.
  - apply field_counter_step_sequenceb_from_sound.
    exact Hseq.
Qed.

Theorem field_counter_step_sequenceb_from_complete :
  forall older views,
    field_counter_step_sequence_from older views ->
    field_counter_step_sequenceb_from older views = true.
Proof.
  intros older views.
  revert older.
  induction views as [|view views IH]; intros older Hseq; simpl in *.
  - reflexivity.
  - destruct Hseq as [Hstep Hrest].
    apply andb_true_iff.
    split.
    + apply field_counter_stepb_complete.
      exact Hstep.
    + apply IH.
      exact Hrest.
Qed.

Theorem field_counter_step_sequenceb_complete :
  forall views,
    field_counter_step_sequence views ->
    field_counter_step_sequenceb views = true.
Proof.
  intros [|view views] Hseq; simpl in *.
  - reflexivity.
  - apply field_counter_step_sequenceb_from_complete.
    exact Hseq.
Qed.

Corollary counter_schema_fits_bitsb_sound :
  forall schema frames,
    counter_schema_fits_bitsb schema frames = true ->
    counter_schema_fits_bits schema frames.
Proof.
  intros schema frames Hfit.
  unfold counter_schema_fits_bitsb, counter_schema_fits_bits in *.
  apply field_counter_step_sequenceb_sound.
  exact Hfit.
Qed.

Corollary counter_schema_fits_bitsb_complete :
  forall schema frames,
    counter_schema_fits_bits schema frames ->
    counter_schema_fits_bitsb schema frames = true.
Proof.
  intros schema frames Hfit.
  unfold counter_schema_fits_bitsb, counter_schema_fits_bits in *.
  apply field_counter_step_sequenceb_complete.
  exact Hfit.
Qed.

Corollary counter_schema_fits_bitsb_singleton :
  forall schema bits,
    counter_schema_fits_bitsb schema [bits] = true.
Proof.
  intros schema bits.
  reflexivity.
Qed.

Theorem prefix12_stronger_than_hi16_lo8b_sound :
  forall frames,
    prefix12_stronger_than_hi16_lo8b frames = true ->
    counter_schema_fits_bitsb hi16_lo8_counter_schema frames = false /\
    counter_schema_fits_bits prefix12_suffix12_counter_schema frames.
Proof.
  intros frames Hstrong.
  unfold prefix12_stronger_than_hi16_lo8b in Hstrong.
  apply andb_true_iff in Hstrong as [Hhi Hprefix].
  apply negb_true_iff in Hhi.
  split.
  - exact Hhi.
  - apply counter_schema_fits_bitsb_sound.
    exact Hprefix.
Qed.

Definition canonical_packet24_from_runs (rs : Runs) : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_runs rs).

Definition canonical_packet24_byte_view_from_runs (rs : Runs) : Packet24ByteView :=
  packet24_byte_view_from_bits (canonical_frame_bits_from_runs rs).

Definition canonical_packet24_nibble_view_from_runs (rs : Runs) : Packet24NibbleView :=
  packet24_nibble_view_from_bits (canonical_frame_bits_from_runs rs).

Definition canonical_packet24_field_view_from_runs (rs : Runs) : Packet24FieldView :=
  packet24_field_view_from_bits (canonical_frame_bits_from_runs rs).

Definition canonical_packet_structure_view_from_runs
    (spec : PacketStructureSpec)
    (rs : Runs)
    : list PacketStructuredFieldValue :=
  packet_structure_view_from_bits spec (canonical_frame_bits_from_runs rs).

Definition canonical_field_counter_view_from_runs
    (schema : CounterSchema)
    (rs : Runs)
    : FieldCounterView :=
  field_counter_view_from_bits schema (canonical_frame_bits_from_runs rs).

Definition canonical_hi16_lo8_counter_view_from_runs
    (rs : Runs)
    : FieldCounterView :=
  canonical_field_counter_view_from_runs hi16_lo8_counter_schema rs.

Definition canonical_prefix12_suffix12_counter_view_from_runs
    (rs : Runs)
    : FieldCounterView :=
  canonical_field_counter_view_from_runs prefix12_suffix12_counter_schema rs.

Record DecodedPacketView := {
  view_bits : list bool;
  view_word : nat;
  view_packet24 : Packet24;
  view_fields : Packet24FieldView
}.

Definition decoded_packet_view_from_classes
    (xs : list PulseClass)
    : DecodedPacketView :=
  {| view_bits := frame_bits_from_classes xs;
     view_word := bits_to_nat (frame_bits_from_classes xs);
     view_packet24 := packet24_from_bits (frame_bits_from_classes xs);
     view_fields := packet24_field_view_from_bits (frame_bits_from_classes xs) |}.

Definition decoded_packet_view_from_runs
    (rs : Runs)
    : DecodedPacketView :=
  decoded_packet_view_from_classes (canonical_normalized_pulse_classes rs).

Theorem classes_of_bits_suffix_word_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    bits_to_nat (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      bits_to_nat (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_packet24_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet24_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      packet24_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_field_value_alias :
  forall bits suffix1 suffix2 spec,
    bits <> [] ->
    field_value spec (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      field_value spec (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 spec Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_byte_view_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet24_byte_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      packet24_byte_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_nibble_view_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet24_nibble_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      packet24_nibble_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_field_view_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet24_field_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      packet24_field_view_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_counter_view_alias :
  forall bits suffix1 suffix2 schema,
    bits <> [] ->
    field_counter_view_from_bits schema
      (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
    field_counter_view_from_bits schema
      (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 schema Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_view_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    decoded_packet_view_from_classes (classes_of_bits bits ++ suffix1) =
      decoded_packet_view_from_classes (classes_of_bits bits ++ suffix2).
Proof.
  intros bits suffix1 suffix2 Hbits.
  unfold decoded_packet_view_from_classes.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem decoded_packet_view_noninjective :
  forall bits,
    bits <> ([] : list bool) ->
    exists xs ys,
      xs <> ys /\
      decoded_packet_view_from_classes xs = decoded_packet_view_from_classes ys.
Proof.
  intros bits Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - apply classes_of_bits_suffix_view_alias.
    exact Hbits.
Qed.

Theorem packet24_field_view_noninjective :
  forall bits,
    bits <> ([] : list bool) ->
    exists xs ys,
      xs <> ys /\
      packet24_field_view_from_bits (frame_bits_from_classes xs) =
        packet24_field_view_from_bits (frame_bits_from_classes ys).
Proof.
  intros bits Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - apply classes_of_bits_suffix_field_view_alias.
    exact Hbits.
Qed.

Theorem field_counter_view_noninjective :
  forall bits schema,
    bits <> ([] : list bool) ->
    exists xs ys,
      xs <> ys /\
      field_counter_view_from_bits schema (frame_bits_from_classes xs) =
        field_counter_view_from_bits schema (frame_bits_from_classes ys).
Proof.
  intros bits schema Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - apply classes_of_bits_suffix_counter_view_alias.
    exact Hbits.
Qed.

Theorem decoded_packet_view_infinite_tail_family :
  forall bits n1 n2,
    bits <> ([] : list bool) ->
    decoded_packet_view_from_classes
      (classes_of_bits bits ++ repeat MarkShort n1) =
    decoded_packet_view_from_classes
      (classes_of_bits bits ++ repeat MarkShort n2).
Proof.
  intros bits n1 n2 Hbits.
  apply classes_of_bits_suffix_view_alias.
  exact Hbits.
Qed.

Theorem decoded_packet_view_tail_family_distinct :
  forall bits n1 n2,
    bits <> ([] : list bool) ->
    n1 <> n2 ->
    classes_of_bits bits ++ repeat MarkShort n1 <>
      classes_of_bits bits ++ repeat MarkShort n2.
Proof.
  intros bits n1 n2 Hbits Hneq.
  apply packet_alias_classes_tail_family_distinct.
  - exact Hbits.
  - exact Hneq.
Qed.

Theorem pulse_base_from_runs_canonical :
  forall rs,
    canonical_pulse_base_from_runs rs = pulse_base_from_runs rs.
Proof.
  intro rs.
  unfold canonical_pulse_base_from_runs, pulse_base_from_runs.
  rewrite active_run_lengths_canonical_runs.
  reflexivity.
Qed.

Theorem canonical_runs_prefix_false_invariant :
  forall n rs,
    canonical_runs ((false, n) :: rs) = canonical_runs rs.
Proof.
  intros n rs.
  unfold canonical_runs.
  reflexivity.
Qed.

Lemma strip_trailing_false_runs_app_false :
  forall rs n,
    strip_trailing_false_runs (rs ++ [(false, n)]) = strip_trailing_false_runs rs.
Proof.
  intros rs n.
  unfold strip_trailing_false_runs.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma strip_leading_false_runs_app_false :
  forall rs n,
    strip_leading_false_runs (rs ++ [(false, n)]) =
      match strip_leading_false_runs rs with
      | [] => []
      | rs' => rs' ++ [(false, n)]
      end.
Proof.
  induction rs as [|(b, m) rs IH]; intro n; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + exact (IH n).
Qed.

Theorem canonical_runs_suffix_false_invariant :
  forall n rs,
    canonical_runs (rs ++ [(false, n)]) = canonical_runs rs.
Proof.
  intros n rs.
  unfold canonical_runs.
  rewrite strip_leading_false_runs_app_false.
  destruct (strip_leading_false_runs rs) as [|r rs'] eqn:Hlead.
  - reflexivity.
  - simpl.
    replace (r :: rs' ++ [(false, n)]) with ((r :: rs') ++ [(false, n)]) by reflexivity.
    apply strip_trailing_false_runs_app_false.
Qed.

Theorem strip_leading_false_runs_scale_commute :
  forall factor rs,
    strip_leading_false_runs (scale_runs factor rs) =
      scale_runs factor (strip_leading_false_runs rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Theorem strip_trailing_false_runs_scale_commute :
  forall factor rs,
    strip_trailing_false_runs (scale_runs factor rs) =
      scale_runs factor (strip_trailing_false_runs rs).
Proof.
  intros factor rs.
  unfold strip_trailing_false_runs.
  rewrite <- scale_runs_rev.
  rewrite strip_leading_false_runs_scale_commute.
  rewrite scale_runs_rev.
  reflexivity.
Qed.

Theorem canonical_runs_scale_commute :
  forall factor rs,
    canonical_runs (scale_runs factor rs) =
      scale_runs factor (canonical_runs rs).
Proof.
  intros factor rs.
  unfold canonical_runs.
  rewrite strip_leading_false_runs_scale_commute.
  rewrite strip_trailing_false_runs_scale_commute.
  reflexivity.
Qed.

Lemma min_list_from_scale :
  forall factor current xs,
    min_list_from (factor * current) (map (Nat.mul factor) xs) =
      factor * min_list_from current xs.
Proof.
  intros factor current xs.
  revert current.
  induction xs as [|x xs IH]; intros current; simpl.
  - reflexivity.
  - rewrite Nat.mul_min_distr_l.
    rewrite IH.
    reflexivity.
Qed.

Lemma min_list_default_scale_nonempty :
  forall factor xs,
    xs <> [] ->
    min_list_default 1 (map (Nat.mul factor) xs) =
      factor * min_list_default 1 xs.
Proof.
  intros factor xs Hnonempty.
  destruct xs as [|x xs'].
  - contradiction.
  - simpl.
    apply min_list_from_scale.
Qed.

Theorem pulse_base_from_runs_scale :
  forall factor rs,
    active_run_lengths rs <> [] ->
    pulse_base_from_runs (scale_runs factor rs) =
      factor * pulse_base_from_runs rs.
Proof.
  intros factor rs Hactive.
  unfold pulse_base_from_runs.
  rewrite active_run_lengths_scale.
  apply min_list_default_scale_nonempty.
  exact Hactive.
Qed.

Lemma ltb_scale_left :
  forall factor n m,
    0 < factor ->
    Nat.ltb (factor * n) (factor * m) = Nat.ltb n m.
Proof.
  intros factor n m Hfactor.
  destruct (Nat.ltb n m) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_lt.
    apply (proj1 (Nat.mul_lt_mono_pos_l factor n m Hfactor)).
    exact Hlt.
  - apply Nat.ltb_ge in Hlt.
    apply Nat.ltb_ge.
    apply Nat.mul_le_mono_l.
    exact Hlt.
Qed.

Lemma scale_two_base :
  forall factor base,
    2 * (factor * base) = factor * (2 * base).
Proof.
  intros factor base.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm 2 factor).
  rewrite <- Nat.mul_assoc.
  reflexivity.
Qed.

Lemma scale_ten_base :
  forall factor base,
    10 * (factor * base) = factor * (10 * base).
Proof.
  intros factor base.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm 10 factor).
  rewrite <- Nat.mul_assoc.
  reflexivity.
Qed.

Theorem classify_run_with_base_scale_invariant :
  forall factor base r,
    0 < factor ->
    classify_run_with_base (factor * base) (scale_run factor r) =
      classify_run_with_base base r.
Proof.
  intros factor base [b n] Hfactor.
  destruct b; cbn [classify_run_with_base scale_run].
  - rewrite scale_two_base.
    rewrite ltb_scale_left by exact Hfactor.
    reflexivity.
  - rewrite scale_two_base.
    rewrite ltb_scale_left by exact Hfactor.
    destruct (Nat.ltb n (2 * base)) eqn:Hshort.
    + reflexivity.
    + rewrite scale_ten_base.
      rewrite ltb_scale_left by exact Hfactor.
      reflexivity.
Qed.

Theorem classify_runs_with_base_scale_invariant :
  forall factor base rs,
    0 < factor ->
    classify_runs_with_base (factor * base) (scale_runs factor rs) =
      classify_runs_with_base base rs.
Proof.
  intros factor base rs Hfactor.
  induction rs as [|r rs IH]; simpl.
  - reflexivity.
  - rewrite classify_run_with_base_scale_invariant by exact Hfactor.
    rewrite IH.
    reflexivity.
Qed.

Theorem pulse_classes_from_scaled_runs_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    classify_runs_with_base
      (pulse_base_from_runs (scale_runs factor rs))
      (scale_runs factor rs) =
    classify_runs_with_base (pulse_base_from_runs rs) rs.
Proof.
  intros factor rs Hfactor Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  apply classify_runs_with_base_scale_invariant.
  exact Hfactor.
Qed.

Corollary pulse_classes_from_doubled_runs_invariant :
  forall rs,
    active_run_lengths rs <> [] ->
    classify_runs_with_base
      (pulse_base_from_runs (scale_runs 2 rs))
      (scale_runs 2 rs) =
    classify_runs_with_base (pulse_base_from_runs rs) rs.
Proof.
  intros rs Hactive.
  apply pulse_classes_from_scaled_runs_invariant.
  - lia.
  - exact Hactive.
Qed.

Theorem classify_runs_with_base_length :
  forall base rs,
    length (classify_runs_with_base base rs) = length rs.
Proof.
  intros base rs.
  unfold classify_runs_with_base.
  rewrite length_map.
  reflexivity.
Qed.

Lemma active_run_lengths_positive :
  forall rs,
    runs_positive rs = true ->
    Forall (fun n => 0 < n) (active_run_lengths rs).
Proof.
  induction rs as [|(b, n) rs IH]; intro Hpos.
  - constructor.
  - simpl in Hpos.
    destruct b.
    + destruct n; try discriminate.
      simpl.
      constructor.
      * lia.
      * apply IH.
        exact Hpos.
    + destruct n; try discriminate.
      apply IH.
      exact Hpos.
Qed.

Lemma min_list_from_positive :
  forall current xs,
    0 < current ->
    Forall (fun n => 0 < n) xs ->
    0 < min_list_from current xs.
Proof.
  intros current xs Hcurrent Hpos.
  revert current Hcurrent.
  induction Hpos as [|x xs Hx Hxs IH]; intros current Hcurrent; simpl.
  - exact Hcurrent.
  - assert (Hmin : 0 < Nat.min current x).
    {
      destruct current, x; simpl in *; lia.
    }
    apply IH.
    exact Hmin.
Qed.

Lemma min_list_default_positive :
  forall default xs,
    0 < default ->
    Forall (fun n => 0 < n) xs ->
    0 < min_list_default default xs.
Proof.
  intros default xs Hdefault Hpos.
  destruct xs as [|x xs'].
  - simpl.
    exact Hdefault.
  - simpl.
    inversion Hpos as [|x' xs'' Hx Hxs]; subst.
    apply min_list_from_positive.
    + exact Hx.
    + exact Hxs.
Qed.

Theorem pulse_base_from_runs_positive :
  forall rs,
    runs_positive rs = true ->
    0 < pulse_base_from_runs rs.
Proof.
  intros rs Hpos.
  unfold pulse_base_from_runs.
  apply min_list_default_positive.
  - lia.
  - apply active_run_lengths_positive.
    exact Hpos.
Qed.

Corollary normalized_pulse_classes_length :
  forall rs,
    length (normalized_pulse_classes rs) = length rs.
Proof.
  intros rs.
  unfold normalized_pulse_classes.
  apply classify_runs_with_base_length.
Qed.

Theorem normalized_pulse_classes_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor rs) = normalized_pulse_classes rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold normalized_pulse_classes.
  apply pulse_classes_from_scaled_runs_invariant.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary normalized_pulse_classes_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor1 rs) =
      normalized_pulse_classes (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (normalized_pulse_classes rs).
  - apply normalized_pulse_classes_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply normalized_pulse_classes_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem normalized_pulse_classes_scale_separated :
  forall factor1 factor2 rs1 rs2,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs1 <> [] ->
    active_run_lengths rs2 <> [] ->
    normalized_pulse_classes rs1 <> normalized_pulse_classes rs2 ->
    normalized_pulse_classes (scale_runs factor1 rs1) <>
      normalized_pulse_classes (scale_runs factor2 rs2).
Proof.
  intros factor1 factor2 rs1 rs2 Hfactor1 Hfactor2 Hactive1 Hactive2 Hneq Heq.
  apply Hneq.
  rewrite <- (normalized_pulse_classes_scale_invariant factor1 rs1 Hfactor1 Hactive1).
  rewrite <- (normalized_pulse_classes_scale_invariant factor2 rs2 Hfactor2 Hactive2).
  exact Heq.
Qed.

Corollary normalized_pulse_classes_double_triple_equal :
  forall rs,
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs 2 rs) =
      normalized_pulse_classes (scale_runs 3 rs).
Proof.
  intros rs Hactive.
  apply normalized_pulse_classes_pairwise_scale_equal.
  - lia.
  - lia.
  - exact Hactive.
Qed.

Theorem pulse_base_from_runs_scale_strict_order :
  forall factor1 factor2 rs,
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    pulse_base_from_runs (scale_runs factor1 rs) <
      pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hlt Hpos Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  assert (Hbase : 0 < pulse_base_from_runs rs).
  {
    apply pulse_base_from_runs_positive.
    exact Hpos.
  }
  apply (proj1 (Nat.mul_lt_mono_pos_r (pulse_base_from_runs rs) factor1 factor2 Hbase)).
  exact Hlt.
Qed.

Theorem normalized_pulse_classes_equal_but_bases_ordered :
  forall factor1 factor2 rs,
    0 < factor1 ->
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor1 rs) =
      normalized_pulse_classes (scale_runs factor2 rs) /\
    pulse_base_from_runs (scale_runs factor1 rs) <
      pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hlt Hpos Hactive.
  split.
  - apply normalized_pulse_classes_pairwise_scale_equal.
    + exact Hfactor1.
    + lia.
    + exact Hactive.
  - apply pulse_base_from_runs_scale_strict_order.
    + exact Hlt.
    + exact Hpos.
    + exact Hactive.
Qed.

Corollary normalized_pulse_classes_double_triple_same_but_bases_ordered :
  forall rs,
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs 2 rs) =
      normalized_pulse_classes (scale_runs 3 rs) /\
    pulse_base_from_runs (scale_runs 2 rs) <
      pulse_base_from_runs (scale_runs 3 rs).
Proof.
  intros rs Hpos Hactive.
  apply normalized_pulse_classes_equal_but_bases_ordered.
  - lia.
  - lia.
  - exact Hpos.
  - exact Hactive.
Qed.

Corollary canonical_normalized_pulse_classes_prefix_false_invariant :
  forall n rs,
    canonical_normalized_pulse_classes ((false, n) :: rs) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros n rs.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_prefix_false_invariant.
  reflexivity.
Qed.

Corollary canonical_normalized_pulse_classes_suffix_false_invariant :
  forall n rs,
    canonical_normalized_pulse_classes (rs ++ [(false, n)]) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros n rs.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_suffix_false_invariant.
  reflexivity.
Qed.

Theorem canonical_normalized_pulse_classes_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor rs) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_scale_commute.
  apply normalized_pulse_classes_scale_invariant.
  - exact Hfactor.
  - rewrite active_run_lengths_canonical_runs.
    exact Hactive.
Qed.

Theorem canonical_frame_bits_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_frame_bits_from_runs (scale_runs factor rs) =
      canonical_frame_bits_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_frame_bits_from_runs, frame_bits_from_classes.
  rewrite canonical_normalized_pulse_classes_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary canonical_frame_bits_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_frame_bits_from_runs (scale_runs factor1 rs) =
      canonical_frame_bits_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_frame_bits_from_runs rs).
  - apply canonical_frame_bits_from_runs_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_frame_bits_from_runs_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem canonical_frame_word_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_frame_word_from_runs (scale_runs factor rs) =
      canonical_frame_word_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_frame_word_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet24_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet24_from_runs (scale_runs factor rs) =
      canonical_packet24_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_packet24_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet24_byte_view_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet24_byte_view_from_runs (scale_runs factor rs) =
      canonical_packet24_byte_view_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_packet24_byte_view_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet24_nibble_view_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet24_nibble_view_from_runs (scale_runs factor rs) =
      canonical_packet24_nibble_view_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_packet24_nibble_view_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet24_field_view_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet24_field_view_from_runs (scale_runs factor rs) =
      canonical_packet24_field_view_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_packet24_field_view_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet_structure_view_from_runs_scale_invariant :
  forall factor spec rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet_structure_view_from_runs spec (scale_runs factor rs) =
      canonical_packet_structure_view_from_runs spec rs.
Proof.
  intros factor spec rs Hfactor Hactive.
  unfold canonical_packet_structure_view_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_field_counter_view_from_runs_scale_invariant :
  forall factor schema rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_field_counter_view_from_runs schema (scale_runs factor rs) =
      canonical_field_counter_view_from_runs schema rs.
Proof.
  intros factor schema rs Hfactor Hactive.
  unfold canonical_field_counter_view_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary canonical_packet24_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_packet24_from_runs (scale_runs factor1 rs) =
      canonical_packet24_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_packet24_from_runs rs).
  - apply canonical_packet24_from_runs_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_packet24_from_runs_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Corollary canonical_packet_structure_view_pairwise_scale_equal :
  forall factor1 factor2 spec rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_packet_structure_view_from_runs spec (scale_runs factor1 rs) =
      canonical_packet_structure_view_from_runs spec (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 spec rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_packet_structure_view_from_runs spec rs).
  - apply canonical_packet_structure_view_from_runs_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_packet_structure_view_from_runs_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.


Corollary canonical_normalized_pulse_classes_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs) =
      canonical_normalized_pulse_classes (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_normalized_pulse_classes rs).
  - apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem canonical_normalized_pulse_classes_scale_separated :
  forall factor1 factor2 rs1 rs2,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs1 <> [] ->
    active_run_lengths rs2 <> [] ->
    canonical_normalized_pulse_classes rs1 <>
      canonical_normalized_pulse_classes rs2 ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs1) <>
      canonical_normalized_pulse_classes (scale_runs factor2 rs2).
Proof.
  intros factor1 factor2 rs1 rs2 Hfactor1 Hfactor2 Hactive1 Hactive2 Hneq Heq.
  apply Hneq.
  rewrite <- (canonical_normalized_pulse_classes_scale_invariant factor1 rs1 Hfactor1 Hactive1).
  rewrite <- (canonical_normalized_pulse_classes_scale_invariant factor2 rs2 Hfactor2 Hactive2).
  exact Heq.
Qed.

Theorem canonical_normalized_pulse_classes_equal_but_bases_ordered :
  forall factor1 factor2 rs,
    0 < factor1 ->
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs) =
      canonical_normalized_pulse_classes (scale_runs factor2 rs) /\
    canonical_pulse_base_from_runs (scale_runs factor1 rs) <
      canonical_pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hlt Hpos Hactive.
  split.
  - apply canonical_normalized_pulse_classes_pairwise_scale_equal.
    + exact Hfactor1.
    + lia.
    + exact Hactive.
  - rewrite pulse_base_from_runs_canonical.
    rewrite pulse_base_from_runs_canonical.
    apply pulse_base_from_runs_scale_strict_order.
    + exact Hlt.
    + exact Hpos.
    + exact Hactive.
Qed.

Corollary canonical_normalized_pulse_classes_double_triple_same_but_bases_ordered :
  forall rs,
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs 2 rs) =
      canonical_normalized_pulse_classes (scale_runs 3 rs) /\
    canonical_pulse_base_from_runs (scale_runs 2 rs) <
      canonical_pulse_base_from_runs (scale_runs 3 rs).
Proof.
  intros rs Hpos Hactive.
  apply canonical_normalized_pulse_classes_equal_but_bases_ordered.
  - lia.
  - lia.
  - exact Hpos.
  - exact Hactive.
Qed.

