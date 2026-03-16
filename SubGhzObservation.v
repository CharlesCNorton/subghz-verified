From Stdlib Require Import List Bool Arith Lia.

Import ListNotations.

Require Import SubGhzCore SubGhzFamilies.

Definition Power := nat.
Definition PowerTrace := list Power.

Fixpoint take_power (n : nat) (xs : PowerTrace) : PowerTrace :=
  match n, xs with
  | O, _ => []
  | S n', [] => []
  | S n', x :: xs' => x :: take_power n' xs'
  end.

Fixpoint drop_power (n : nat) (xs : PowerTrace) : PowerTrace :=
  match n, xs with
  | O, _ => xs
  | S n', [] => []
  | S n', _ :: xs' => drop_power n' xs'
  end.

Lemma take_drop_power :
  forall n xs,
    take_power n xs ++ drop_power n xs = xs.
Proof.
  induction n as [|n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Definition window_above_threshold (threshold sample : Power) : bool :=
  Nat.leb threshold sample.

Definition threshold_trace (threshold : Power) (xs : PowerTrace) : Trace :=
  map (window_above_threshold threshold) xs.

Definition active_count_from_powers
    (span threshold : nat)
    (xs : PowerTrace)
    : nat :=
  window_active_count span (threshold_trace threshold xs).

Definition first_dense_power_window
    (span threshold min_active : nat)
    (xs : PowerTrace)
    : option nat :=
  first_dense_window span min_active (threshold_trace threshold xs).

Definition has_dense_power_window
    (span threshold min_active : nat)
    (xs : PowerTrace)
    : bool :=
  match first_dense_power_window span threshold min_active xs with
  | Some _ => true
  | None => false
  end.

Definition first_active_power_window
    (threshold : nat)
    (xs : PowerTrace)
    : option nat :=
  first_true (threshold_trace threshold xs).

Definition last_active_power_window
    (threshold : nat)
    (xs : PowerTrace)
    : option nat :=
  last_true (threshold_trace threshold xs).

Definition pulse_runs_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Runs :=
  rle_trace (threshold_trace threshold xs).

Definition pulse_base_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  pulse_base_from_runs (pulse_runs_from_powers threshold xs).

Definition pulse_classes_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list PulseClass :=
  let rs := pulse_runs_from_powers threshold xs in
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Lemma drop_threshold_trace :
  forall n threshold xs,
    drop n (threshold_trace threshold xs) = threshold_trace threshold (drop_power n xs).
Proof.
  induction n as [|n IH]; intros threshold xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + apply IH.
Qed.

Theorem first_dense_power_window_sound :
  forall span threshold min_active xs idx,
    first_dense_power_window span threshold min_active xs = Some idx ->
    idx <= length xs /\
    min_active <= active_count_from_powers span threshold (drop_power idx xs).
Proof.
  intros span threshold min_active xs idx H.
  unfold first_dense_power_window in H.
  destruct (first_dense_window_sound span min_active (threshold_trace threshold xs) idx H)
    as [Hidx Hcount].
  split.
  - unfold threshold_trace in Hidx.
    rewrite length_map in Hidx.
    exact Hidx.
  - unfold active_count_from_powers.
    rewrite <- drop_threshold_trace.
    exact Hcount.
Qed.

Theorem first_active_power_window_sound :
  forall threshold xs idx,
    first_active_power_window threshold xs = Some idx ->
    idx < length xs /\
    nth idx (threshold_trace threshold xs) false = true /\
    (forall j, j < idx -> nth j (threshold_trace threshold xs) false = false).
Proof.
  intros threshold xs idx H.
  unfold first_active_power_window in H.
  destruct (first_true_sound (threshold_trace threshold xs) idx H)
    as [Hlt [Hnth Hprefix]].
  split.
  - unfold threshold_trace in Hlt.
    rewrite length_map in Hlt.
    exact Hlt.
  - split.
    + exact Hnth.
    + exact Hprefix.
Qed.

Theorem last_active_power_window_sound :
  forall threshold xs idx,
    last_active_power_window threshold xs = Some idx ->
    idx < length xs /\
    nth idx (threshold_trace threshold xs) false = true /\
    (forall j,
        idx < j ->
        j < length xs ->
        nth j (threshold_trace threshold xs) false = false).
Proof.
  intros threshold xs idx H.
  unfold last_active_power_window in H.
  destruct (last_true_sound (threshold_trace threshold xs) idx H)
    as [Hlt [Hnth Hsuffix]].
  split.
  - unfold threshold_trace in Hlt.
    rewrite length_map in Hlt.
    exact Hlt.
  - split.
    + exact Hnth.
    + intros j Hij Hjlen.
      apply Hsuffix.
      * exact Hij.
      * unfold threshold_trace.
        rewrite length_map.
        exact Hjlen.
Qed.

Theorem flatten_pulse_runs_from_powers :
  forall threshold xs,
    flatten_runs (pulse_runs_from_powers threshold xs) = threshold_trace threshold xs.
Proof.
  intros threshold xs.
  unfold pulse_runs_from_powers.
  apply flatten_rle_trace.
Qed.

Theorem pulse_runs_from_powers_positive :
  forall threshold xs,
    runs_positive (pulse_runs_from_powers threshold xs) = true.
Proof.
  intros threshold xs.
  unfold pulse_runs_from_powers.
  apply rle_trace_positive.
Qed.

Theorem pulse_base_from_powers_positive :
  forall threshold xs,
    0 < pulse_base_from_powers threshold xs.
Proof.
  intros threshold xs.
  unfold pulse_base_from_powers.
  apply pulse_base_from_runs_positive.
  apply pulse_runs_from_powers_positive.
Qed.

Theorem pulse_classes_from_powers_length :
  forall threshold xs,
    length (pulse_classes_from_powers threshold xs) =
      length (pulse_runs_from_powers threshold xs).
Proof.
  intros threshold xs.
  unfold pulse_classes_from_powers.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem first_dense_power_window_complete_from_suffix :
  forall prefix suffix span threshold min_active,
    min_active <= active_count_from_powers span threshold suffix ->
    exists idx,
      first_dense_power_window span threshold min_active (prefix ++ suffix) = Some idx.
Proof.
  intros prefix suffix span threshold min_active Hcount.
  unfold first_dense_power_window, active_count_from_powers in *.
  unfold threshold_trace.
  rewrite map_app.
  apply first_dense_window_complete_from_suffix.
  exact Hcount.
Qed.

Corollary has_dense_power_window_complete_from_suffix :
  forall prefix suffix span threshold min_active,
    min_active <= active_count_from_powers span threshold suffix ->
    has_dense_power_window span threshold min_active (prefix ++ suffix) = true.
Proof.
  intros prefix suffix span threshold min_active Hcount.
  destruct
    (first_dense_power_window_complete_from_suffix
       prefix suffix span threshold min_active Hcount) as [idx Hidx].
  unfold has_dense_power_window.
  rewrite Hidx.
  reflexivity.
Qed.

Theorem first_dense_power_window_complete :
  forall prefix block suffix span threshold min_active,
    span <= length block ->
    min_active <= active_count_from_powers span threshold block ->
    exists idx,
      first_dense_power_window span threshold min_active (prefix ++ block ++ suffix) = Some idx.
Proof.
  intros prefix block suffix span threshold min_active Hspan Hdense.
  unfold first_dense_power_window, active_count_from_powers in *.
  unfold threshold_trace.
  rewrite map_app, map_app.
  eapply first_dense_window_complete.
  - rewrite length_map.
    exact Hspan.
  - exact Hdense.
Qed.

Theorem active_count_from_powers_threshold_monotone :
  forall span low high xs,
    low <= high ->
    active_count_from_powers span high xs <= active_count_from_powers span low xs.
Proof.
  induction span as [|span IH]; intros low high xs Hle.
  - unfold active_count_from_powers, window_active_count.
    simpl.
    lia.
  - unfold active_count_from_powers, window_active_count in *.
    destruct xs as [|x xs']; simpl.
    + apply Nat.le_refl.
    + unfold window_above_threshold.
      destruct (Nat.leb high x) eqn:Hhigh;
      destruct (Nat.leb low x) eqn:Hlow; simpl.
      * specialize (IH low high xs' Hle).
        lia.
      * apply Nat.leb_le in Hhigh.
        apply Nat.leb_gt in Hlow.
        lia.
      * eapply Nat.le_trans.
        -- apply IH.
           exact Hle.
        -- lia.
      * apply IH.
        exact Hle.
Qed.

Theorem has_dense_power_window_threshold_monotone :
  forall span low high min_active xs,
    low <= high ->
    has_dense_power_window span high min_active xs = true ->
    has_dense_power_window span low min_active xs = true.
Proof.
  intros span low high min_active xs Hle Hdetect.
  unfold has_dense_power_window in Hdetect.
  destruct (first_dense_power_window span high min_active xs) eqn:Hhigh.
  - apply first_dense_power_window_sound in Hhigh.
    destruct Hhigh as [Hidx Hcount].
    assert (Hmono :
      active_count_from_powers span high (drop_power n xs) <=
      active_count_from_powers span low (drop_power n xs)).
    {
      apply active_count_from_powers_threshold_monotone.
      exact Hle.
    }
    assert (Hlowcount :
      min_active <= active_count_from_powers span low (drop_power n xs)).
    {
      lia.
    }
    unfold has_dense_power_window.
    rewrite <- (take_drop_power n xs).
    apply has_dense_power_window_complete_from_suffix.
    exact Hlowcount.
  - discriminate.
Qed.

Definition scale_powers (factor : nat) (xs : PowerTrace) : PowerTrace :=
  map (Nat.mul factor) xs.

Definition offset_powers (offset : nat) (xs : PowerTrace) : PowerTrace :=
  map (Nat.add offset) xs.

Definition canonical_pulse_runs_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Runs :=
  canonical_runs (pulse_runs_from_powers threshold xs).

Definition canonical_pulse_base_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  canonical_pulse_base_from_runs (pulse_runs_from_powers threshold xs).

Definition canonical_pulse_classes_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list PulseClass :=
  canonical_normalized_pulse_classes (pulse_runs_from_powers threshold xs).

Definition canonical_frame_bits_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list bool :=
  frame_bits_from_classes (canonical_pulse_classes_from_powers threshold xs).

Definition canonical_frame_word_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  bits_to_nat (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_byte_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24ByteView :=
  packet24_byte_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_nibble_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24NibbleView :=
  packet24_nibble_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_field_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24FieldView :=
  packet24_field_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet_structure_view_from_powers
    (spec : PacketStructureSpec)
    (threshold : nat)
    (xs : PowerTrace)
    : list PacketStructuredFieldValue :=
  packet_structure_view_from_bits spec
    (canonical_frame_bits_from_powers threshold xs).

Definition canonical_field_counter_view_from_powers
    (schema : CounterSchema)
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  field_counter_view_from_bits schema (canonical_frame_bits_from_powers threshold xs).

Definition canonical_hi16_lo8_counter_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  canonical_field_counter_view_from_powers hi16_lo8_counter_schema threshold xs.

Definition canonical_prefix12_suffix12_counter_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  canonical_field_counter_view_from_powers prefix12_suffix12_counter_schema threshold xs.

Definition canonical_field_counter_fresh_from_powers
    (schema : CounterSchema)
    (state : FieldCounterState)
    (threshold : nat)
    (xs : PowerTrace)
    : bool :=
  field_counter_fresh state (canonical_field_counter_view_from_powers schema threshold xs).

Definition power_within_margin (margin x y : nat) : Prop :=
  x <= y + margin /\ y <= x + margin.

Fixpoint power_trace_within_margin
    (margin : nat)
    (xs ys : PowerTrace)
    : Prop :=
  match xs, ys with
  | [], [] => True
  | x :: xs', y :: ys' =>
      power_within_margin margin x y /\
      power_trace_within_margin margin xs' ys'
  | _, _ => False
  end.

Definition threshold_stable_sample
    (threshold margin sample : nat)
    : Prop :=
  sample + margin < threshold \/ threshold + margin <= sample.

Definition threshold_shift_up_stable_sample
    (threshold drift sample : nat)
    : Prop :=
  sample < threshold \/ threshold + drift <= sample.

Fixpoint power_trace_threshold_shift_up_stable
    (threshold drift : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_shift_up_stable_sample threshold drift x /\
      power_trace_threshold_shift_up_stable threshold drift xs'
  end.

Definition threshold_shift_down_stable_sample
    (threshold drift sample : nat)
    : Prop :=
  sample + drift < threshold \/ threshold <= sample.

Fixpoint power_trace_threshold_shift_down_stable
    (threshold drift : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_shift_down_stable_sample threshold drift x /\
      power_trace_threshold_shift_down_stable threshold drift xs'
  end.

Fixpoint power_trace_threshold_stable
    (threshold margin : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_stable_sample threshold margin x /\
      power_trace_threshold_stable threshold margin xs'
  end.

Lemma window_above_threshold_scale_invariant :
  forall factor threshold sample,
    0 < factor ->
    window_above_threshold (factor * threshold) (factor * sample) =
      window_above_threshold threshold sample.
Proof.
  intros factor threshold sample Hfactor.
  unfold window_above_threshold.
  destruct (Nat.leb threshold sample) eqn:Hbase.
  - apply Nat.leb_le in Hbase.
    apply Nat.leb_le.
    apply (proj1 (Nat.mul_le_mono_pos_l threshold sample factor Hfactor)).
    exact Hbase.
  - apply Nat.leb_gt in Hbase.
    apply Nat.leb_gt.
    apply (proj1 (Nat.mul_lt_mono_pos_l factor sample threshold Hfactor)).
    exact Hbase.
Qed.

Theorem threshold_trace_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    threshold_trace (factor * threshold) (scale_powers factor xs) =
      threshold_trace threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite window_above_threshold_scale_invariant by exact Hfactor.
    rewrite IH by exact Hfactor.
    reflexivity.
Qed.

Theorem active_count_from_powers_scale_invariant :
  forall factor span threshold xs,
    0 < factor ->
    active_count_from_powers span (factor * threshold) (scale_powers factor xs) =
      active_count_from_powers span threshold xs.
Proof.
  intros factor span threshold xs Hfactor.
  unfold active_count_from_powers.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem first_dense_power_window_scale_invariant :
  forall factor span threshold min_active xs,
    0 < factor ->
    first_dense_power_window span (factor * threshold) min_active
      (scale_powers factor xs) =
      first_dense_power_window span threshold min_active xs.
Proof.
  intros factor span threshold min_active xs Hfactor.
  unfold first_dense_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem first_active_power_window_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    first_active_power_window (factor * threshold) (scale_powers factor xs) =
      first_active_power_window threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold first_active_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem last_active_power_window_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    last_active_power_window (factor * threshold) (scale_powers factor xs) =
      last_active_power_window threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold last_active_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem pulse_runs_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    pulse_runs_from_powers (factor * threshold) (scale_powers factor xs) =
      pulse_runs_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold pulse_runs_from_powers.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_runs_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_runs_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_runs_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_runs_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_base_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_base_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_base_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_base_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_classes_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_classes_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Lemma window_above_threshold_offset_invariant :
  forall offset threshold sample,
    window_above_threshold (offset + threshold) (offset + sample) =
      window_above_threshold threshold sample.
Proof.
  intros offset threshold sample.
  unfold window_above_threshold.
  destruct (Nat.leb threshold sample) eqn:Hbase.
  - apply Nat.leb_le in Hbase.
    apply Nat.leb_le.
    lia.
  - apply Nat.leb_gt in Hbase.
    apply Nat.leb_gt.
    lia.
Qed.

Theorem threshold_trace_offset_invariant :
  forall offset threshold xs,
    threshold_trace (offset + threshold) (offset_powers offset xs) =
      threshold_trace threshold xs.
Proof.
  intros offset threshold xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite window_above_threshold_offset_invariant.
    rewrite IH.
    reflexivity.
Qed.

Lemma window_above_threshold_upward_drift_invariant :
  forall drift threshold sample,
    threshold_shift_up_stable_sample threshold drift sample ->
    window_above_threshold (threshold + drift) sample =
      window_above_threshold threshold sample.
Proof.
  intros drift threshold sample Hstable.
  unfold window_above_threshold.
  destruct (Nat.leb (threshold + drift) sample) eqn:Hup;
    destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
  - apply Nat.leb_le in Hup.
    apply Nat.leb_gt in Hbase.
    lia.
  - destruct Hstable as [Hbelow | Habove].
    + apply Nat.leb_gt in Hup.
      apply Nat.leb_le in Hbase.
      lia.
    + apply Nat.leb_gt in Hup.
      apply Nat.leb_le in Hbase.
      lia.
Qed.

Theorem threshold_trace_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    threshold_trace (threshold + drift) xs =
      threshold_trace threshold xs.
Proof.
  intros drift threshold xs Hstable.
  induction xs as [|x xs IH]; simpl in *.
  - reflexivity.
  - destruct Hstable as [Hx Hxs].
    rewrite window_above_threshold_upward_drift_invariant by exact Hx.
    rewrite IH by exact Hxs.
    reflexivity.
Qed.

Lemma window_above_threshold_downward_drift_invariant :
  forall drift threshold sample,
    drift <= threshold ->
    threshold_shift_down_stable_sample threshold drift sample ->
    window_above_threshold (threshold - drift) sample =
      window_above_threshold threshold sample.
Proof.
  intros drift threshold sample Hdrift Hstable.
  unfold window_above_threshold.
  destruct Hstable as [Hbelow | Habove].
  - destruct (Nat.leb (threshold - drift) sample) eqn:Hdown;
      destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
    + apply Nat.leb_le in Hdown.
      apply Nat.leb_gt in Hbase.
      lia.
    + apply Nat.leb_gt in Hdown.
      apply Nat.leb_le in Hbase.
      lia.
  - destruct (Nat.leb (threshold - drift) sample) eqn:Hdown;
      destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
    + apply Nat.leb_le in Hdown.
      apply Nat.leb_gt in Hbase.
      lia.
    + apply Nat.leb_gt in Hdown.
      apply Nat.leb_le in Hbase.
      lia.
Qed.

Theorem threshold_trace_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    threshold_trace (threshold - drift) xs =
      threshold_trace threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  induction xs as [|x xs IH]; simpl in *.
  - reflexivity.
  - destruct Hstable as [Hx Hxs].
    rewrite window_above_threshold_downward_drift_invariant
      by exact Hdrift || exact Hx.
    rewrite IH by exact Hdrift || exact Hxs.
    reflexivity.
Qed.

Theorem pulse_runs_from_powers_offset_invariant :
  forall offset threshold xs,
    pulse_runs_from_powers (offset + threshold) (offset_powers offset xs) =
      pulse_runs_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold pulse_runs_from_powers.
  rewrite threshold_trace_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_pulse_classes_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_pulse_classes_from_powers.
  rewrite pulse_runs_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_frame_bits_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite canonical_pulse_classes_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_frame_bits_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite canonical_pulse_classes_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_frame_word_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_frame_word_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Lemma window_above_threshold_margin_invariant :
  forall threshold margin x y,
    power_within_margin margin x y ->
    threshold_stable_sample threshold margin x ->
    window_above_threshold threshold y =
      window_above_threshold threshold x.
Proof.
  intros threshold margin x y [Hxy Hyx] Hstable.
  destruct Hstable as [Hbelow | Habove].
  - assert (Hx : window_above_threshold threshold x = false).
    {
      unfold window_above_threshold.
      apply Nat.leb_gt.
      lia.
    }
    assert (Hy : window_above_threshold threshold y = false).
    {
      unfold window_above_threshold.
      apply Nat.leb_gt.
      lia.
    }
    rewrite Hx, Hy.
    reflexivity.
  - assert (Hx : window_above_threshold threshold x = true).
    {
      unfold window_above_threshold.
      apply Nat.leb_le.
      lia.
    }
    assert (Hy : window_above_threshold threshold y = true).
    {
      unfold window_above_threshold.
      apply Nat.leb_le.
      lia.
    }
    rewrite Hx, Hy.
    reflexivity.
Qed.

Theorem threshold_trace_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    threshold_trace threshold ys = threshold_trace threshold xs.
Proof.
  intros threshold margin xs.
  induction xs as [|x xs IH]; intros ys Hmargin Hstable.
  - destruct ys as [|y ys']; simpl in *.
    + reflexivity.
    + contradiction.
  - destruct ys as [|y ys']; simpl in *.
    + contradiction.
    + destruct Hmargin as [Hxy Hmargin'].
      destruct Hstable as [Hxstable Hstable'].
      rewrite (window_above_threshold_margin_invariant
                 threshold margin x y Hxy Hxstable).
      rewrite (IH ys' Hmargin' Hstable').
      reflexivity.
Qed.

Theorem first_dense_power_window_margin_invariant :
  forall span threshold margin xs ys min_active,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    first_dense_power_window span threshold min_active ys =
      first_dense_power_window span threshold min_active xs.
Proof.
  intros span threshold margin xs ys min_active Hmargin Hstable.
  unfold first_dense_power_window.
  rewrite (threshold_trace_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem pulse_runs_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    pulse_runs_from_powers threshold ys = pulse_runs_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold pulse_runs_from_powers.
  rewrite (threshold_trace_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_pulse_classes_from_powers threshold ys =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_pulse_classes_from_powers.
  rewrite (pulse_runs_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_frame_bits_from_powers threshold ys =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite (canonical_pulse_classes_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_frame_word_from_powers threshold ys =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_byte_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_byte_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_nibble_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_field_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_field_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_scale_invariant :
  forall spec factor threshold xs,
    0 < factor ->
    canonical_packet_structure_view_from_powers spec (factor * threshold) (scale_powers factor xs) =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec factor threshold xs Hfactor.
  unfold canonical_packet_structure_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_scale_invariant :
  forall schema factor threshold xs,
    0 < factor ->
    canonical_field_counter_view_from_powers schema (factor * threshold) (scale_powers factor xs) =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema factor threshold xs Hfactor.
  unfold canonical_field_counter_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_from_powers threshold ys =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_byte_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_byte_view_from_powers threshold ys =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_nibble_view_from_powers threshold ys =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_field_view_from_powers threshold ys =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_field_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_margin_invariant :
  forall spec threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet_structure_view_from_powers spec threshold ys =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_margin_invariant :
  forall schema threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_field_counter_view_from_powers schema threshold ys =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema threshold margin xs ys Hmargin Hstable.
  unfold canonical_field_counter_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet24_byte_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_byte_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_nibble_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_field_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_field_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_offset_invariant :
  forall spec offset threshold xs,
    canonical_packet_structure_view_from_powers spec (offset + threshold) (offset_powers offset xs) =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec offset threshold xs.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_offset_invariant :
  forall schema offset threshold xs,
    canonical_field_counter_view_from_powers schema (offset + threshold) (offset_powers offset xs) =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema offset threshold xs.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_frame_bits_from_powers (threshold + drift) xs =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes,
    canonical_pulse_classes_from_powers, pulse_runs_from_powers.
  rewrite threshold_trace_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_frame_word_from_powers (threshold + drift) xs =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_packet24_from_powers (threshold + drift) xs =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_upward_drift_invariant :
  forall spec drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_packet_structure_view_from_powers spec (threshold + drift) xs =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec drift threshold xs Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_upward_drift_invariant :
  forall schema drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_field_counter_view_from_powers schema (threshold + drift) xs =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema drift threshold xs Hstable.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_frame_bits_from_powers (threshold - drift) xs =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes,
    canonical_pulse_classes_from_powers, pulse_runs_from_powers.
  rewrite threshold_trace_downward_drift_invariant by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_frame_word_from_powers (threshold - drift) xs =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_packet24_from_powers (threshold - drift) xs =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_downward_drift_invariant :
  forall spec drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_packet_structure_view_from_powers spec (threshold - drift) xs =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec drift threshold xs Hdrift Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_downward_drift_invariant :
  forall schema drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_field_counter_view_from_powers schema (threshold - drift) xs =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema drift threshold xs Hdrift Hstable.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Definition Byte := nat.
Definition ByteStream := list Byte.
Definition IQPair := (Byte * Byte)%type.
Definition IQTrace := list IQPair.

Definition IQObserver (A : Type) := ByteStream -> A.

Definition iq_observer_injective
    {A : Type}
    (obs : IQObserver A)
    : Prop :=
  forall xs ys, obs xs = obs ys -> xs = ys.

Fixpoint bytes_to_iq (xs : ByteStream) : IQTrace :=
  match xs with
  | i :: q :: xs' => (i, q) :: bytes_to_iq xs'
  | _ => []
  end.

Definition centered_twice_abs (b : Byte) : nat :=
  let doubled := b + b in
  if Nat.leb doubled 255 then 255 - doubled else doubled - 255.

Definition iq_pair_energy (pair : IQPair) : Power :=
  let '(i, q) := pair in
  let di := centered_twice_abs i in
  let dq := centered_twice_abs q in
  di * di + dq * dq.

Definition iq_byte_pair_energy (i q : Byte) : Power :=
  let di := centered_twice_abs i in
  let dq := centered_twice_abs q in
  di * di + dq * dq.

Theorem iq_byte_pair_energy_sym :
  forall i q,
    iq_byte_pair_energy i q = iq_byte_pair_energy q i.
Proof.
  intros i q.
  unfold iq_byte_pair_energy.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Definition iq_energy_trace (xs : ByteStream) : PowerTrace :=
  map iq_pair_energy (bytes_to_iq xs).

Fixpoint sum_powers (xs : PowerTrace) : Power :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_powers xs'
  end.

Fixpoint power_window_sums_fuel
    (fuel window_pairs : nat)
    (xs : PowerTrace)
    : PowerTrace :=
  match fuel with
  | O => []
  | S fuel' =>
      match window_pairs with
      | O => []
      | S _ =>
          if Nat.ltb (length xs) window_pairs then
            []
          else
            sum_powers (take_power window_pairs xs)
              :: power_window_sums_fuel fuel' window_pairs (drop_power window_pairs xs)
      end
  end.

Definition power_window_sums (window_pairs : nat) (xs : PowerTrace) : PowerTrace :=
  power_window_sums_fuel (length xs) window_pairs xs.

Fixpoint iq_window_energy_trace_acc
    (window_pairs remaining acc : nat)
    (xs : ByteStream)
    (rev_windows : PowerTrace)
    : PowerTrace :=
  match xs with
  | i :: q :: xs' =>
      match remaining with
      | O => rev rev_windows
      | S remaining' =>
          let acc' := acc + iq_byte_pair_energy i q in
          match remaining' with
          | O =>
              iq_window_energy_trace_acc window_pairs window_pairs 0 xs'
                (acc' :: rev_windows)
          | S _ =>
              iq_window_energy_trace_acc window_pairs remaining' acc' xs'
                rev_windows
          end
      end
  | _ => rev rev_windows
  end.

Definition iq_window_energy_trace
    (window_pairs : nat)
    (xs : ByteStream)
    : PowerTrace :=
  match window_pairs with
  | O => []
  | S _ => iq_window_energy_trace_acc window_pairs window_pairs 0 xs []
  end.

Definition first_dense_iq_window
    (window_pairs span threshold min_active : nat)
    (xs : ByteStream)
    : option nat :=
  first_dense_power_window span threshold min_active
    (iq_window_energy_trace window_pairs xs).

Definition has_dense_iq_window
    (window_pairs span threshold min_active : nat)
    (xs : ByteStream)
    : bool :=
  has_dense_power_window span threshold min_active
    (iq_window_energy_trace window_pairs xs).

Definition first_active_iq_window
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : option nat :=
  first_active_power_window threshold
    (iq_window_energy_trace window_pairs xs).

Definition last_active_iq_window
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : option nat :=
  last_active_power_window threshold
    (iq_window_energy_trace window_pairs xs).

Definition pulse_runs_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Runs :=
  pulse_runs_from_powers threshold
    (iq_window_energy_trace window_pairs xs).

Definition pulse_base_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  pulse_base_from_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition pulse_classes_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PulseClass :=
  let rs := pulse_runs_from_iq window_pairs threshold xs in
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Definition canonical_pulse_runs_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Runs :=
  canonical_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_pulse_base_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  canonical_pulse_base_from_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_pulse_classes_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PulseClass :=
  canonical_normalized_pulse_classes (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_frame_bits_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list bool :=
  frame_bits_from_classes (canonical_pulse_classes_from_iq window_pairs threshold xs).

Definition canonical_frame_word_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  bits_to_nat (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_byte_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24ByteView :=
  packet24_byte_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_nibble_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24NibbleView :=
  packet24_nibble_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_field_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24FieldView :=
  packet24_field_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition decoded_packet_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : DecodedPacketView :=
  {| view_bits := canonical_frame_bits_from_iq window_pairs threshold xs;
     view_word := canonical_frame_word_from_iq window_pairs threshold xs;
     view_packet24 := canonical_packet24_from_iq window_pairs threshold xs;
     view_fields := canonical_packet24_field_view_from_iq window_pairs threshold xs |}.

Definition canonical_packet_structure_view_from_iq
    (spec : PacketStructureSpec)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PacketStructuredFieldValue :=
  packet_structure_view_from_bits spec
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_field_counter_view_from_iq
    (schema : CounterSchema)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  field_counter_view_from_bits schema (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_hi16_lo8_counter_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  canonical_field_counter_view_from_iq hi16_lo8_counter_schema window_pairs threshold xs.

Definition canonical_prefix12_suffix12_counter_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  canonical_field_counter_view_from_iq prefix12_suffix12_counter_schema window_pairs threshold xs.

Definition canonical_field_counter_fresh_from_iq
    (schema : CounterSchema)
    (state : FieldCounterState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : bool :=
  field_counter_fresh state
    (canonical_field_counter_view_from_iq schema window_pairs threshold xs).

Definition canonical_packet_schema_fresh_from_iq
    (kind : PacketSchemaKind)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : bool :=
  packet_schema_fresh_from_bits kind state
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet_schema_descriptor_structure_from_iq
    (descriptor : PacketSchemaDescriptor)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PacketStructuredFieldValue :=
  packet_schema_descriptor_structure_from_bits
    descriptor
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet_schema_descriptor_fresh_from_iq
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : bool :=
  packet_schema_descriptor_fresh_from_bits
    descriptor state
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition packet_schema_descriptor_observation_from_iq
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : PacketSchemaDescriptorObservation :=
  {| descriptor_observation_structure :=
       canonical_packet_schema_descriptor_structure_from_iq
         descriptor window_pairs threshold xs;
     descriptor_observation_fresh :=
       canonical_packet_schema_descriptor_fresh_from_iq
         descriptor state window_pairs threshold xs |}.

Definition iq_observer_factors_through_decoded_view
    {A : Type}
    (window_pairs threshold : nat)
    (obs : IQObserver A)
    : Prop :=
  exists view_obs : DecodedPacketView -> A,
    forall xs,
      obs xs = view_obs (decoded_packet_view_from_iq window_pairs threshold xs).

Definition iq_observer_factors_through_packet_schema_descriptor_observation
    {A : Type}
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (obs : IQObserver A)
    : Prop :=
  exists descriptor_obs : PacketSchemaDescriptorObservation -> A,
    forall xs,
      obs xs =
        descriptor_obs
          (packet_schema_descriptor_observation_from_iq
             descriptor state window_pairs threshold xs).

Definition canonical_packet_schema_descriptor_fresh_sequence_from_iq
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : list bool :=
  packet_schema_descriptor_fresh_sequence_from_bits
    descriptor state
    (map (canonical_frame_bits_from_iq window_pairs threshold) xss).

Definition iq_window_energy_equivalent
    (window_pairs : nat)
    (xs ys : ByteStream)
    : Prop :=
  iq_window_energy_trace window_pairs xs =
    iq_window_energy_trace window_pairs ys.

Definition iq_window_energy_within_margin
    (window_pairs margin : nat)
    (xs ys : ByteStream)
    : Prop :=
  power_trace_within_margin margin
    (iq_window_energy_trace window_pairs xs)
    (iq_window_energy_trace window_pairs ys).

Definition iq_window_energy_threshold_stable
    (window_pairs threshold margin : nat)
    (xs : ByteStream)
    : Prop :=
  power_trace_threshold_stable threshold margin
    (iq_window_energy_trace window_pairs xs).

Theorem iq_window_energy_equivalent_implies_pulse_runs_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    pulse_runs_from_iq window_pairs threshold xs =
      pulse_runs_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold iq_window_energy_equivalent, pulse_runs_from_iq in *.
  rewrite Heq.
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_frame_bits_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_frame_bits_from_iq window_pairs threshold xs =
      canonical_frame_bits_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold canonical_frame_bits_from_iq, canonical_pulse_classes_from_iq.
  rewrite (iq_window_energy_equivalent_implies_pulse_runs_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_frame_word_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_frame_word_from_iq window_pairs threshold xs =
      canonical_frame_word_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold canonical_frame_word_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_structure_invariant :
  forall spec window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_packet_structure_view_from_iq spec window_pairs threshold xs =
      canonical_packet_structure_view_from_iq spec window_pairs threshold ys.
Proof.
  intros spec window_pairs threshold xs ys Heq.
  unfold canonical_packet_structure_view_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_counter_view_invariant :
  forall schema window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_field_counter_view_from_iq schema window_pairs threshold xs =
      canonical_field_counter_view_from_iq schema window_pairs threshold ys.
Proof.
  intros schema window_pairs threshold xs ys Heq.
  unfold canonical_field_counter_view_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_decoded_view_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    decoded_packet_view_from_iq window_pairs threshold xs =
      decoded_packet_view_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold decoded_packet_view_from_iq,
    canonical_frame_word_from_iq,
    canonical_packet24_from_iq,
    canonical_packet24_field_view_from_iq.
  rewrite
    (iq_window_energy_equivalent_implies_frame_bits_invariant
       window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_schema_descriptor_structure_invariant :
  forall descriptor window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_packet_schema_descriptor_structure_from_iq
      descriptor window_pairs threshold xs =
      canonical_packet_schema_descriptor_structure_from_iq
        descriptor window_pairs threshold ys.
Proof.
  intros descriptor window_pairs threshold xs ys Heq.
  unfold canonical_packet_schema_descriptor_structure_from_iq,
    packet_schema_descriptor_structure_from_bits.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_schema_fresh_invariant :
  forall kind state window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_packet_schema_fresh_from_iq
      kind state window_pairs threshold xs =
      canonical_packet_schema_fresh_from_iq
        kind state window_pairs threshold ys.
Proof.
  intros kind state window_pairs threshold xs ys Heq.
  unfold canonical_packet_schema_fresh_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_schema_descriptor_fresh_invariant :
  forall descriptor state window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_packet_schema_descriptor_fresh_from_iq
      descriptor state window_pairs threshold xs =
      canonical_packet_schema_descriptor_fresh_from_iq
        descriptor state window_pairs threshold ys.
Proof.
  intros descriptor state window_pairs threshold xs ys Heq.
  unfold canonical_packet_schema_descriptor_fresh_from_iq,
    packet_schema_descriptor_fresh_from_bits.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_schema_descriptor_observation_invariant :
  forall descriptor state window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    packet_schema_descriptor_observation_from_iq
      descriptor state window_pairs threshold xs =
      packet_schema_descriptor_observation_from_iq
        descriptor state window_pairs threshold ys.
Proof.
  intros descriptor state window_pairs threshold xs ys Heq.
  unfold packet_schema_descriptor_observation_from_iq.
  rewrite
    (iq_window_energy_equivalent_implies_packet_schema_descriptor_structure_invariant
       descriptor window_pairs threshold xs ys Heq).
  rewrite
    (iq_window_energy_equivalent_implies_packet_schema_descriptor_fresh_invariant
       descriptor state window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_factored_decoded_view_observer_invariant :
  forall (A : Type) (obs : IQObserver A) window_pairs threshold xs ys,
    iq_observer_factors_through_decoded_view window_pairs threshold obs ->
    iq_window_energy_equivalent window_pairs xs ys ->
    obs xs = obs ys.
Proof.
  intros A obs window_pairs threshold xs ys [view_obs Hobs] Heq.
  rewrite (Hobs xs).
  rewrite (Hobs ys).
  rewrite
    (iq_window_energy_equivalent_implies_decoded_view_invariant
       window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_factored_packet_schema_descriptor_observer_invariant :
  forall (A : Type) (obs : IQObserver A)
         descriptor state window_pairs threshold xs ys,
    iq_observer_factors_through_packet_schema_descriptor_observation
      descriptor state window_pairs threshold obs ->
    iq_window_energy_equivalent window_pairs xs ys ->
    obs xs = obs ys.
Proof.
  intros A obs descriptor state window_pairs threshold xs ys
    [descriptor_obs Hobs] Heq.
  rewrite (Hobs xs).
  rewrite (Hobs ys).
  rewrite
    (iq_window_energy_equivalent_implies_packet_schema_descriptor_observation_invariant
       descriptor state window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_single_pair_swap :
  forall i q,
    iq_window_energy_equivalent 1 [i; q] [q; i].
Proof.
  intros i q.
  unfold iq_window_energy_equivalent, iq_window_energy_trace.
  simpl.
  rewrite iq_byte_pair_energy_sym.
  reflexivity.
Qed.

Theorem decoded_view_factored_iq_observer_single_pair_swap_blindness :
  forall (A : Type) (obs : IQObserver A) (threshold : nat) (i q : Byte),
    iq_observer_factors_through_decoded_view 1 threshold obs ->
    obs [i; q] = obs [q; i].
Proof.
  intros A obs threshold i q Hfactor.
  apply
    (iq_window_energy_equivalent_factored_decoded_view_observer_invariant
       A obs 1 threshold [i; q] [q; i]).
  - exact Hfactor.
  - apply iq_window_energy_equivalent_single_pair_swap.
Qed.

Theorem packet_schema_descriptor_factored_iq_observer_single_pair_swap_blindness :
  forall (A : Type) (obs : IQObserver A) descriptor state
         (threshold : nat) (i q : Byte),
    iq_observer_factors_through_packet_schema_descriptor_observation
      descriptor state 1 threshold obs ->
    obs [i; q] = obs [q; i].
Proof.
  intros A obs descriptor state threshold i q Hfactor.
  apply
    (iq_window_energy_equivalent_factored_packet_schema_descriptor_observer_invariant
       A obs descriptor state 1 threshold [i; q] [q; i]).
  - exact Hfactor.
  - apply iq_window_energy_equivalent_single_pair_swap.
Qed.

Theorem decoded_view_factored_iq_observer_noninjective :
  forall (A : Type) (obs : IQObserver A) (threshold : nat) (i q : Byte),
    iq_observer_factors_through_decoded_view 1 threshold obs ->
    i <> q ->
    exists xs ys,
      xs <> ys /\ obs xs = obs ys.
Proof.
  intros A obs threshold i q Hfactor Hneq.
  exists [i; q].
  exists [q; i].
  split.
  - intro Heq.
    inversion Heq.
    contradiction.
  - apply
      (decoded_view_factored_iq_observer_single_pair_swap_blindness
         A obs threshold i q).
    exact Hfactor.
Qed.

Theorem packet_schema_descriptor_factored_iq_observer_noninjective :
  forall (A : Type) (obs : IQObserver A) descriptor state
         (threshold : nat) (i q : Byte),
    iq_observer_factors_through_packet_schema_descriptor_observation
      descriptor state 1 threshold obs ->
    i <> q ->
    exists xs ys,
      xs <> ys /\ obs xs = obs ys.
Proof.
  intros A obs descriptor state threshold i q Hfactor Hneq.
  exists [i; q].
  exists [q; i].
  split.
  - intro Heq.
    inversion Heq.
    contradiction.
  - apply
      (packet_schema_descriptor_factored_iq_observer_single_pair_swap_blindness
         A obs descriptor state threshold i q).
    exact Hfactor.
Qed.

Theorem decoded_view_factored_iq_observer_not_injective :
  forall (A : Type) (obs : IQObserver A) (threshold : nat) (i q : Byte),
    iq_observer_factors_through_decoded_view 1 threshold obs ->
    i <> q ->
    ~ iq_observer_injective obs.
Proof.
  intros A obs threshold i q Hfactor Hneq Hinjective.
  destruct
    (decoded_view_factored_iq_observer_noninjective
       A obs threshold i q Hfactor Hneq) as [xs [ys [Hxy Hobs]]].
  apply Hxy.
  apply Hinjective.
  exact Hobs.
Qed.

Theorem packet_schema_descriptor_factored_iq_observer_not_injective :
  forall (A : Type) (obs : IQObserver A) descriptor state
         (threshold : nat) (i q : Byte),
    iq_observer_factors_through_packet_schema_descriptor_observation
      descriptor state 1 threshold obs ->
    i <> q ->
    ~ iq_observer_injective obs.
Proof.
  intros A obs descriptor state threshold i q Hfactor Hneq Hinjective.
  destruct
    (packet_schema_descriptor_factored_iq_observer_noninjective
       A obs descriptor state threshold i q Hfactor Hneq)
    as [xs [ys [Hxy Hobs]]].
  apply Hxy.
  apply Hinjective.
  exact Hobs.
Qed.

Theorem canonical_frame_bits_from_iq_margin_invariant :
  forall window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_frame_bits_from_iq window_pairs threshold ys =
      canonical_frame_bits_from_iq window_pairs threshold xs.
Proof.
  intros window_pairs threshold margin xs ys Hmargin Hstable.
  unfold iq_window_energy_within_margin, iq_window_energy_threshold_stable in *.
  change
    (canonical_frame_bits_from_iq window_pairs threshold ys)
    with (canonical_frame_bits_from_powers
            threshold
            (iq_window_energy_trace window_pairs ys)).
  change
    (canonical_frame_bits_from_iq window_pairs threshold xs)
    with (canonical_frame_bits_from_powers
            threshold
            (iq_window_energy_trace window_pairs xs)).
  eapply canonical_frame_bits_from_powers_margin_invariant;
    eassumption.
Qed.

Theorem canonical_packet_structure_view_from_iq_margin_invariant :
  forall spec window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_packet_structure_view_from_iq spec window_pairs threshold ys =
      canonical_packet_structure_view_from_iq spec window_pairs threshold xs.
Proof.
  intros spec window_pairs threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_structure_view_from_iq.
  rewrite (canonical_frame_bits_from_iq_margin_invariant
             window_pairs threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_iq_margin_invariant :
  forall schema window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_field_counter_view_from_iq schema window_pairs threshold ys =
      canonical_field_counter_view_from_iq schema window_pairs threshold xs.
Proof.
  intros schema window_pairs threshold margin xs ys Hmargin Hstable.
  unfold canonical_field_counter_view_from_iq.
  rewrite (canonical_frame_bits_from_iq_margin_invariant
             window_pairs threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet_schema_fresh_from_iq_margin_invariant :
  forall kind state window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_packet_schema_fresh_from_iq kind state window_pairs threshold ys =
      canonical_packet_schema_fresh_from_iq kind state window_pairs threshold xs.
Proof.
  intros kind state window_pairs threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_schema_fresh_from_iq.
  rewrite (canonical_frame_bits_from_iq_margin_invariant
             window_pairs threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet_schema_descriptor_structure_from_iq_margin_invariant :
  forall descriptor window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_packet_schema_descriptor_structure_from_iq
      descriptor window_pairs threshold ys =
      canonical_packet_schema_descriptor_structure_from_iq
        descriptor window_pairs threshold xs.
Proof.
  intros descriptor window_pairs threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_schema_descriptor_structure_from_iq,
    packet_schema_descriptor_structure_from_bits.
  rewrite (canonical_frame_bits_from_iq_margin_invariant
             window_pairs threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet_schema_descriptor_fresh_from_iq_margin_invariant :
  forall descriptor state window_pairs threshold margin xs ys,
    iq_window_energy_within_margin window_pairs margin xs ys ->
    iq_window_energy_threshold_stable window_pairs threshold margin xs ->
    canonical_packet_schema_descriptor_fresh_from_iq
      descriptor state window_pairs threshold ys =
      canonical_packet_schema_descriptor_fresh_from_iq
        descriptor state window_pairs threshold xs.
Proof.
  intros descriptor state window_pairs threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_schema_descriptor_fresh_from_iq,
    packet_schema_descriptor_fresh_from_bits.
  rewrite (canonical_frame_bits_from_iq_margin_invariant
             window_pairs threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Definition frame_bits_sequence_from_iq
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : list (list bool) :=
  map (canonical_frame_bits_from_iq window_pairs threshold) xss.

Definition packet_structure_profile_from_iq_sequence
    (spec : PacketStructureSpec)
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : list PacketStructuredFieldProfile :=
  packet_structure_profile_from_bits_sequence spec
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition counter_schema_fits_iqb
    (schema : CounterSchema)
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : bool :=
  counter_schema_fits_bitsb schema
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition counter_schema_fit_report_from_iq_sequence
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : CounterSchemaFitReport :=
  counter_schema_fit_report_from_bits
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition counter_schema_classification_code_from_iq_sequence
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : nat :=
  counter_schema_classification_code_from_bits
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition prefix12_stronger_than_hi16_lo8_from_iqb
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : bool :=
  prefix12_stronger_than_hi16_lo8b
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Theorem counter_schema_fits_iqb_sound :
  forall schema window_pairs threshold xss,
    counter_schema_fits_iqb schema window_pairs threshold xss = true ->
    counter_schema_fits_bits schema
      (frame_bits_sequence_from_iq window_pairs threshold xss).
Proof.
  intros schema window_pairs threshold xss Hfit.
  unfold counter_schema_fits_iqb.
  apply counter_schema_fits_bitsb_sound.
  exact Hfit.
Qed.

Theorem counter_schema_classification_code_from_iq_sequence_singleton :
  forall window_pairs threshold xs,
    counter_schema_classification_code_from_iq_sequence window_pairs threshold [xs] = 3.
Proof.
  intros window_pairs threshold xs.
  unfold counter_schema_classification_code_from_iq_sequence,
    counter_schema_classification_code_from_bits,
    counter_schema_fit_report_from_bits,
    frame_bits_sequence_from_iq.
  simpl.
  reflexivity.
Qed.

Theorem prefix12_stronger_than_hi16_lo8_from_iqb_sound :
  forall window_pairs threshold xss,
    prefix12_stronger_than_hi16_lo8_from_iqb window_pairs threshold xss = true ->
    counter_schema_fits_bitsb hi16_lo8_counter_schema
      (frame_bits_sequence_from_iq window_pairs threshold xss) = false /\
    counter_schema_fits_bits prefix12_suffix12_counter_schema
      (frame_bits_sequence_from_iq window_pairs threshold xss).
Proof.
  intros window_pairs threshold xss Hstrong.
  unfold prefix12_stronger_than_hi16_lo8_from_iqb in Hstrong.
  apply prefix12_stronger_than_hi16_lo8b_sound.
  exact Hstrong.
Qed.

Theorem frame_bits_sequence_invariant_between_iq_regimes_implies_packet_structure_profile_invariant :
  forall spec window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    packet_structure_profile_from_iq_sequence spec window_pairs1 threshold1 xss =
      packet_structure_profile_from_iq_sequence spec window_pairs2 threshold2 xss.
Proof.
  intros spec window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  unfold packet_structure_profile_from_iq_sequence.
  rewrite Hbits.
  reflexivity.
Qed.

Definition iq_window_energy_sequence_equivalent
    (window_pairs : nat)
    (xss yss : list ByteStream)
    : Prop :=
  Forall2 (iq_window_energy_equivalent window_pairs) xss yss.

Definition iq_window_energy_sequence_within_margin
    (window_pairs margin : nat)
    (xss yss : list ByteStream)
    : Prop :=
  Forall2 (iq_window_energy_within_margin window_pairs margin) xss yss.

Definition iq_window_energy_sequence_threshold_stable
    (window_pairs threshold margin : nat)
    (xss : list ByteStream)
    : Prop :=
  Forall (iq_window_energy_threshold_stable window_pairs threshold margin) xss.

Theorem iq_window_energy_sequence_equivalent_implies_frame_bits_sequence_invariant :
  forall window_pairs threshold xss yss,
    iq_window_energy_sequence_equivalent window_pairs xss yss ->
    frame_bits_sequence_from_iq window_pairs threshold xss =
      frame_bits_sequence_from_iq window_pairs threshold yss.
Proof.
  intros window_pairs threshold xss yss Hequiv.
  induction Hequiv; simpl.
  - reflexivity.
  - rewrite
      (iq_window_energy_equivalent_implies_frame_bits_invariant
         window_pairs threshold x y H).
    rewrite IHHequiv.
    reflexivity.
Qed.

Theorem iq_window_energy_sequence_margin_implies_frame_bits_sequence_invariant :
  forall window_pairs threshold margin xss yss,
    iq_window_energy_sequence_within_margin window_pairs margin xss yss ->
    iq_window_energy_sequence_threshold_stable window_pairs threshold margin xss ->
    frame_bits_sequence_from_iq window_pairs threshold yss =
      frame_bits_sequence_from_iq window_pairs threshold xss.
Proof.
  intros window_pairs threshold margin xss yss Hmargin Hstable.
  revert yss Hmargin.
  induction Hstable as [|xs xss Hstable_head Hstable_tail IH]; intros yss Hmargin.
  - inversion Hmargin; reflexivity.
  - inversion Hmargin as [|x y xss' yss' Hmargin_xy Hmargin_rest]; subst; simpl.
    rewrite
      (canonical_frame_bits_from_iq_margin_invariant
         window_pairs threshold margin xs y Hmargin_xy Hstable_head).
    rewrite (IH _ Hmargin_rest).
    reflexivity.
Qed.

Theorem iq_window_energy_sequence_equivalent_implies_packet_structure_profile_invariant :
  forall spec window_pairs threshold xss yss,
    iq_window_energy_sequence_equivalent window_pairs xss yss ->
    packet_structure_profile_from_iq_sequence spec window_pairs threshold xss =
      packet_structure_profile_from_iq_sequence spec window_pairs threshold yss.
Proof.
  intros spec window_pairs threshold xss yss Hequiv.
  unfold packet_structure_profile_from_iq_sequence.
  rewrite (iq_window_energy_sequence_equivalent_implies_frame_bits_sequence_invariant
             window_pairs threshold xss yss Hequiv).
  reflexivity.
Qed.

Theorem iq_window_energy_sequence_equivalent_implies_packet_schema_descriptor_profile_invariant :
  forall descriptor window_pairs threshold xss yss,
    iq_window_energy_sequence_equivalent window_pairs xss yss ->
    packet_schema_descriptor_profile_from_bits_sequence
      descriptor
      (frame_bits_sequence_from_iq window_pairs threshold xss) =
      packet_schema_descriptor_profile_from_bits_sequence
        descriptor
        (frame_bits_sequence_from_iq window_pairs threshold yss).
Proof.
  intros descriptor window_pairs threshold xss yss Hequiv.
  rewrite (iq_window_energy_sequence_equivalent_implies_frame_bits_sequence_invariant
             window_pairs threshold xss yss Hequiv).
  reflexivity.
Qed.

Theorem iq_window_energy_sequence_equivalent_implies_packet_schema_descriptor_fresh_sequence_invariant :
  forall descriptor state window_pairs threshold xss yss,
    iq_window_energy_sequence_equivalent window_pairs xss yss ->
    canonical_packet_schema_descriptor_fresh_sequence_from_iq
      descriptor state window_pairs threshold xss =
      canonical_packet_schema_descriptor_fresh_sequence_from_iq
        descriptor state window_pairs threshold yss.
Proof.
  intros descriptor state window_pairs threshold xss yss Hequiv.
  unfold canonical_packet_schema_descriptor_fresh_sequence_from_iq.
  change (map (canonical_frame_bits_from_iq window_pairs threshold) xss)
    with (frame_bits_sequence_from_iq window_pairs threshold xss).
  change (map (canonical_frame_bits_from_iq window_pairs threshold) yss)
    with (frame_bits_sequence_from_iq window_pairs threshold yss).
  rewrite (iq_window_energy_sequence_equivalent_implies_frame_bits_sequence_invariant
             window_pairs threshold xss yss Hequiv).
  reflexivity.
Qed.

Theorem iq_window_energy_sequence_equivalent_implies_counter_schema_classification_invariant :
  forall window_pairs threshold xss yss,
    iq_window_energy_sequence_equivalent window_pairs xss yss ->
    counter_schema_classification_code_from_bits
      (frame_bits_sequence_from_iq window_pairs threshold xss) =
      counter_schema_classification_code_from_bits
        (frame_bits_sequence_from_iq window_pairs threshold yss).
Proof.
  intros window_pairs threshold xss yss Hequiv.
  rewrite (iq_window_energy_sequence_equivalent_implies_frame_bits_sequence_invariant
             window_pairs threshold xss yss Hequiv).
  reflexivity.
Qed.

Theorem iq_window_energy_sequence_margin_implies_packet_schema_descriptor_profile_invariant :
  forall descriptor window_pairs threshold margin xss yss,
    iq_window_energy_sequence_within_margin window_pairs margin xss yss ->
    iq_window_energy_sequence_threshold_stable window_pairs threshold margin xss ->
    packet_schema_descriptor_profile_from_bits_sequence
      descriptor
      (frame_bits_sequence_from_iq window_pairs threshold yss) =
      packet_schema_descriptor_profile_from_bits_sequence
        descriptor
        (frame_bits_sequence_from_iq window_pairs threshold xss).
Proof.
  intros descriptor window_pairs threshold margin xss yss Hmargin Hstable.
  rewrite (iq_window_energy_sequence_margin_implies_frame_bits_sequence_invariant
             window_pairs threshold margin xss yss Hmargin Hstable).
  reflexivity.
Qed.

Theorem iq_window_energy_sequence_margin_implies_packet_schema_descriptor_fresh_sequence_invariant :
  forall descriptor state window_pairs threshold margin xss yss,
    iq_window_energy_sequence_within_margin window_pairs margin xss yss ->
    iq_window_energy_sequence_threshold_stable window_pairs threshold margin xss ->
    canonical_packet_schema_descriptor_fresh_sequence_from_iq
      descriptor state window_pairs threshold yss =
      canonical_packet_schema_descriptor_fresh_sequence_from_iq
        descriptor state window_pairs threshold xss.
Proof.
  intros descriptor state window_pairs threshold margin xss yss Hmargin Hstable.
  unfold canonical_packet_schema_descriptor_fresh_sequence_from_iq.
  change (map (canonical_frame_bits_from_iq window_pairs threshold) yss)
    with (frame_bits_sequence_from_iq window_pairs threshold yss).
  change (map (canonical_frame_bits_from_iq window_pairs threshold) xss)
    with (frame_bits_sequence_from_iq window_pairs threshold xss).
  rewrite (iq_window_energy_sequence_margin_implies_frame_bits_sequence_invariant
             window_pairs threshold margin xss yss Hmargin Hstable).
  reflexivity.
Qed.

Theorem frame_bits_sequence_invariant_between_iq_regimes_implies_packet_schema_descriptor_profile_invariant :
  forall descriptor window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    packet_schema_descriptor_profile_from_bits_sequence
      descriptor
      (frame_bits_sequence_from_iq window_pairs1 threshold1 xss) =
      packet_schema_descriptor_profile_from_bits_sequence
        descriptor
        (frame_bits_sequence_from_iq window_pairs2 threshold2 xss).
Proof.
  intros descriptor window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_sequence_invariant_between_iq_regimes_implies_packet_schema_descriptor_fresh_sequence_invariant :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    canonical_packet_schema_descriptor_fresh_sequence_from_iq
      descriptor state window_pairs1 threshold1 xss =
      canonical_packet_schema_descriptor_fresh_sequence_from_iq
        descriptor state window_pairs2 threshold2 xss.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  unfold canonical_packet_schema_descriptor_fresh_sequence_from_iq.
  change
    (map (canonical_frame_bits_from_iq window_pairs1 threshold1) xss)
    with (frame_bits_sequence_from_iq window_pairs1 threshold1 xss).
  change
    (map (canonical_frame_bits_from_iq window_pairs2 threshold2) xss)
    with (frame_bits_sequence_from_iq window_pairs2 threshold2 xss).
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_sequence_invariant_between_iq_regimes_implies_counter_schema_classification_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    counter_schema_classification_code_from_bits
      (frame_bits_sequence_from_iq window_pairs1 threshold1 xss) =
      counter_schema_classification_code_from_bits
        (frame_bits_sequence_from_iq window_pairs2 threshold2 xss).
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  rewrite Hbits.
  reflexivity.
Qed.

Definition emitter_class_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : EmitterClass :=
  canonical_pulse_classes_from_iq window_pairs threshold xs.

Definition same_emitter_class_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  emitter_class_from_iq window_pairs threshold xs =
    emitter_class_from_iq window_pairs threshold ys.

Definition cross_receiver_invariant_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  canonical_pulse_classes_from_iq window_pairs threshold xs =
    canonical_pulse_classes_from_iq window_pairs threshold ys.

Definition coarse_cross_receiver_invariant_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  coarse_pulse_classes (canonical_pulse_classes_from_iq window_pairs threshold xs) =
    coarse_pulse_classes (canonical_pulse_classes_from_iq window_pairs threshold ys).


Record PulseParseCertificate := {
  certificate_window_pairs : nat;
  certificate_threshold : nat;
  certificate_first_active : option nat;
  certificate_last_active : option nat;
  certificate_runs : Runs;
  certificate_base : nat;
  certificate_classes : list PulseClass
}.

Record FrameParseCertificate := {
  frame_certificate_pulse : PulseParseCertificate;
  frame_certificate_bits : list bool
}.

Definition pulse_parse_certificate_self_consistent
    (cert : PulseParseCertificate)
    : bool :=
  Nat.eqb (certificate_base cert)
    (pulse_base_from_runs (certificate_runs cert))
  &&
  Nat.eqb (length (certificate_classes cert))
    (length (certificate_runs cert))
  &&
  pulse_class_list_eqb
    (certificate_classes cert)
    (classify_runs_with_base
      (certificate_base cert)
      (certificate_runs cert)).

Definition certify_canonical_pulse_parse_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : PulseParseCertificate :=
  let runs := canonical_pulse_runs_from_iq window_pairs threshold xs in
  let base := canonical_pulse_base_from_iq window_pairs threshold xs in
  let classes := canonical_pulse_classes_from_iq window_pairs threshold xs in
  {| certificate_window_pairs := window_pairs;
     certificate_threshold := threshold;
     certificate_first_active :=
       first_active_iq_window window_pairs threshold xs;
     certificate_last_active :=
       last_active_iq_window window_pairs threshold xs;
     certificate_runs := runs;
     certificate_base := base;
     certificate_classes := classes |}.

Definition certify_canonical_frame_parse_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FrameParseCertificate :=
  let pulse_cert := certify_canonical_pulse_parse_from_iq window_pairs threshold xs in
  {| frame_certificate_pulse := pulse_cert;
     frame_certificate_bits :=
       canonical_frame_bits_from_iq window_pairs threshold xs |}.

Definition pulse_parse_certificate_valid
    (window_pairs threshold : nat)
    (xs : ByteStream)
    (cert : PulseParseCertificate)
    : Prop :=
  certificate_window_pairs cert = window_pairs /\
  certificate_threshold cert = threshold /\
  certificate_first_active cert =
    first_active_iq_window window_pairs threshold xs /\
  certificate_last_active cert =
    last_active_iq_window window_pairs threshold xs /\
  certificate_runs cert =
    canonical_pulse_runs_from_iq window_pairs threshold xs /\
  certificate_base cert =
    canonical_pulse_base_from_iq window_pairs threshold xs /\
  certificate_classes cert =
    canonical_pulse_classes_from_iq window_pairs threshold xs /\
  pulse_parse_certificate_self_consistent cert = true.

Definition frame_parse_certificate_valid
    (window_pairs threshold : nat)
    (xs : ByteStream)
    (cert : FrameParseCertificate)
    : Prop :=
  pulse_parse_certificate_valid
    window_pairs threshold xs (frame_certificate_pulse cert) /\
  frame_certificate_bits cert =
    canonical_frame_bits_from_iq window_pairs threshold xs.

Theorem first_dense_iq_window_sound :
  forall window_pairs span threshold min_active xs idx,
    first_dense_iq_window window_pairs span threshold min_active xs = Some idx ->
    idx <= length (iq_window_energy_trace window_pairs xs) /\
    min_active <=
      active_count_from_powers span threshold
        (drop_power idx (iq_window_energy_trace window_pairs xs)).
Proof.
  intros window_pairs span threshold min_active xs idx H.
  unfold first_dense_iq_window in H.
  apply first_dense_power_window_sound in H.
  exact H.
Qed.

Theorem first_active_iq_window_sound :
  forall window_pairs threshold xs idx,
    first_active_iq_window window_pairs threshold xs = Some idx ->
    idx < length (iq_window_energy_trace window_pairs xs) /\
    nth idx
      (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
      false = true /\
    (forall j,
        j < idx ->
        nth j
          (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
          false = false).
Proof.
  intros window_pairs threshold xs idx H.
  unfold first_active_iq_window in H.
  apply first_active_power_window_sound in H.
  exact H.
Qed.

Theorem last_active_iq_window_sound :
  forall window_pairs threshold xs idx,
    last_active_iq_window window_pairs threshold xs = Some idx ->
    idx < length (iq_window_energy_trace window_pairs xs) /\
    nth idx
      (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
      false = true /\
    (forall j,
        idx < j ->
        j < length (iq_window_energy_trace window_pairs xs) ->
        nth j
          (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
          false = false).
Proof.
  intros window_pairs threshold xs idx H.
  unfold last_active_iq_window in H.
  apply last_active_power_window_sound in H.
  exact H.
Qed.

Theorem flatten_pulse_runs_from_iq :
  forall window_pairs threshold xs,
    flatten_runs (pulse_runs_from_iq window_pairs threshold xs) =
      threshold_trace threshold (iq_window_energy_trace window_pairs xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_runs_from_iq.
  apply flatten_pulse_runs_from_powers.
Qed.

Theorem pulse_runs_from_iq_positive :
  forall window_pairs threshold xs,
    runs_positive (pulse_runs_from_iq window_pairs threshold xs) = true.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_runs_from_iq.
  apply pulse_runs_from_powers_positive.
Qed.

Theorem pulse_base_from_iq_positive :
  forall window_pairs threshold xs,
    0 < pulse_base_from_iq window_pairs threshold xs.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_base_from_iq.
  apply pulse_base_from_runs_positive.
  apply pulse_runs_from_iq_positive.
Qed.

Theorem pulse_classes_from_iq_length :
  forall window_pairs threshold xs,
    length (pulse_classes_from_iq window_pairs threshold xs) =
      length (pulse_runs_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_classes_from_iq.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem canonical_pulse_base_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_pulse_base_from_iq window_pairs threshold xs =
      pulse_base_from_iq window_pairs threshold xs.
Proof.
  intros window_pairs threshold xs.
  unfold canonical_pulse_base_from_iq, pulse_base_from_iq.
  apply pulse_base_from_runs_canonical.
Qed.

Theorem canonical_pulse_classes_from_iq_length :
  forall window_pairs threshold xs,
    length (canonical_pulse_classes_from_iq window_pairs threshold xs) =
      length (canonical_pulse_runs_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold canonical_pulse_classes_from_iq, canonical_pulse_runs_from_iq.
  unfold canonical_normalized_pulse_classes, normalized_pulse_classes.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_frame_bits_from_iq window_pairs threshold xs =
      frame_bits_from_classes
        (canonical_pulse_classes_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_frame_word_from_iq window_pairs threshold xs =
      bits_to_nat (canonical_frame_bits_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  reflexivity.
Qed.

Definition frame_bit_count_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  length (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition family_descriptor_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FamilyDescriptor :=
  {| family_object := canonical_pulse_classes_from_iq window_pairs threshold xs;
     family_frame_bits := canonical_frame_bits_from_iq window_pairs threshold xs |}.

Definition semantic_tower_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FamilySemanticTower :=
  {| tower_object := canonical_pulse_classes_from_iq window_pairs threshold xs;
     tower_bits := canonical_frame_bits_from_iq window_pairs threshold xs;
     tower_word := canonical_frame_word_from_iq window_pairs threshold xs;
     tower_packet24 := canonical_packet24_from_iq window_pairs threshold xs;
     tower_fields := canonical_packet24_field_view_from_iq window_pairs threshold xs |}.

Record PacketSchemaDescriptorPhaseSignature := {
  phase_signature_object : CanonicalRFObject;
  phase_signature_frame_bit_count : nat;
  phase_signature_decoded_view : DecodedPacketView;
  phase_signature_schema_observation : PacketSchemaDescriptorObservation
}.

Definition packet_schema_descriptor_phase_signature_from_iq
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : PacketSchemaDescriptorPhaseSignature :=
  {| phase_signature_object :=
       canonical_pulse_classes_from_iq window_pairs threshold xs;
     phase_signature_frame_bit_count :=
       frame_bit_count_from_iq window_pairs threshold xs;
     phase_signature_decoded_view :=
       decoded_packet_view_from_iq window_pairs threshold xs;
     phase_signature_schema_observation :=
       packet_schema_descriptor_observation_from_iq
         descriptor state window_pairs threshold xs |}.

Definition packet24_eqb
    (x y : Packet24)
    : bool :=
  Nat.eqb (packet24_hi x) (packet24_hi y)
  &&
  Nat.eqb (packet24_mid x) (packet24_mid y)
  &&
  Nat.eqb (packet24_lo x) (packet24_lo y).

Definition packet24_byte_view_eqb
    (x y : Packet24ByteView)
    : bool :=
  Nat.eqb (packet24_byte0 x) (packet24_byte0 y)
  &&
  Nat.eqb (packet24_byte1 x) (packet24_byte1 y)
  &&
  Nat.eqb (packet24_byte2 x) (packet24_byte2 y).

Definition packet24_nibble_view_eqb
    (x y : Packet24NibbleView)
    : bool :=
  Nat.eqb (packet24_nibble0 x) (packet24_nibble0 y)
  &&
  Nat.eqb (packet24_nibble1 x) (packet24_nibble1 y)
  &&
  Nat.eqb (packet24_nibble2 x) (packet24_nibble2 y)
  &&
  Nat.eqb (packet24_nibble3 x) (packet24_nibble3 y)
  &&
  Nat.eqb (packet24_nibble4 x) (packet24_nibble4 y)
  &&
  Nat.eqb (packet24_nibble5 x) (packet24_nibble5 y).

Definition packet24_field_view_eqb
    (x y : Packet24FieldView)
    : bool :=
  packet24_byte_view_eqb
    (packet24_fields_bytes x)
    (packet24_fields_bytes y)
  &&
  packet24_nibble_view_eqb
    (packet24_fields_nibbles x)
    (packet24_fields_nibbles y)
  &&
  Nat.eqb (packet24_fields_prefix12 x) (packet24_fields_prefix12 y)
  &&
  Nat.eqb (packet24_fields_suffix12 x) (packet24_fields_suffix12 y).

Definition packet_structured_field_value_eqb
    (x y : PacketStructuredFieldValue)
    : bool :=
  Nat.eqb
    (packet_field_role_code (structured_field_role x))
    (packet_field_role_code (structured_field_role y))
  &&
  Nat.eqb (structured_field_offset x) (structured_field_offset y)
  &&
  Nat.eqb (structured_field_width x) (structured_field_width y)
  &&
  Nat.eqb (structured_field_value x) (structured_field_value y).

Fixpoint packet_structured_field_value_list_eqb
    (xs ys : list PacketStructuredFieldValue)
    : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      packet_structured_field_value_eqb x y
      &&
      packet_structured_field_value_list_eqb xs' ys'
  | _, _ => false
  end.

Definition packet_schema_descriptor_observation_eqb
    (x y : PacketSchemaDescriptorObservation)
    : bool :=
  packet_structured_field_value_list_eqb
    (descriptor_observation_structure x)
    (descriptor_observation_structure y)
  &&
  Bool.eqb
    (descriptor_observation_fresh x)
    (descriptor_observation_fresh y).

Definition decoded_packet_view_eqb
    (x y : DecodedPacketView)
    : bool :=
  bool_list_eqb (view_bits x) (view_bits y)
  &&
  Nat.eqb (view_word x) (view_word y)
  &&
  packet24_eqb (view_packet24 x) (view_packet24 y)
  &&
  packet24_field_view_eqb (view_fields x) (view_fields y).

Definition family_descriptor_eqb
    (x y : FamilyDescriptor)
    : bool :=
  pulse_class_list_eqb (family_object x) (family_object y)
  &&
  bool_list_eqb (family_frame_bits x) (family_frame_bits y).

Definition semantic_tower_eqb
    (x y : FamilySemanticTower)
    : bool :=
  pulse_class_list_eqb (tower_object x) (tower_object y)
  &&
  bool_list_eqb (tower_bits x) (tower_bits y)
  &&
  Nat.eqb (tower_word x) (tower_word y)
  &&
  packet24_eqb (tower_packet24 x) (tower_packet24 y)
  &&
  packet24_field_view_eqb (tower_fields x) (tower_fields y).

Definition packet_schema_descriptor_phase_signature_eqb
    (x y : PacketSchemaDescriptorPhaseSignature)
    : bool :=
  pulse_class_list_eqb
    (phase_signature_object x)
    (phase_signature_object y)
  &&
  Nat.eqb
    (phase_signature_frame_bit_count x)
    (phase_signature_frame_bit_count y)
  &&
  decoded_packet_view_eqb
    (phase_signature_decoded_view x)
    (phase_signature_decoded_view y)
  &&
  packet_schema_descriptor_observation_eqb
    (phase_signature_schema_observation x)
    (phase_signature_schema_observation y).

Definition observed_iq_matches_family
    (base_pattern : Runs)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Prop :=
  canonical_pulse_classes_from_iq window_pairs threshold xs =
    tx_family_object base_pattern.

Theorem observed_iq_matches_family_implies_frame_bits :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_frame_bits_from_iq window_pairs threshold xs =
      canonical_frame_bits_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold observed_iq_matches_family, tx_family_object in Hmatch.
  unfold canonical_frame_bits_from_iq, canonical_frame_bits_from_runs.
  rewrite Hmatch.
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_frame_word :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_frame_word_from_iq window_pairs threshold xs =
      canonical_frame_word_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_frame_word_from_iq, canonical_frame_word_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet24 :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet24_from_iq window_pairs threshold xs =
      canonical_packet24_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet24_from_iq, canonical_packet24_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_field_view :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet24_field_view_from_iq window_pairs threshold xs =
      canonical_packet24_field_view_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet24_field_view_from_iq, canonical_packet24_field_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_decoded_view :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    decoded_packet_view_from_iq window_pairs threshold xs =
      decoded_packet_view_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold decoded_packet_view_from_iq, decoded_packet_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_frame_word
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_packet24
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_field_view
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet_structure :
  forall spec base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet_structure_view_from_iq spec window_pairs threshold xs =
      canonical_packet_structure_view_from_runs spec base_pattern.
Proof.
  intros spec base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet_structure_view_from_iq,
    canonical_packet_structure_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_counter_view :
  forall schema base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_field_counter_view_from_iq schema window_pairs threshold xs =
      canonical_field_counter_view_from_runs schema base_pattern.
Proof.
  intros schema base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_field_counter_view_from_iq, canonical_field_counter_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet_schema_descriptor_structure :
  forall descriptor base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet_schema_descriptor_structure_from_iq
      descriptor window_pairs threshold xs =
      canonical_packet_schema_descriptor_structure_from_runs
        descriptor base_pattern.
Proof.
  intros descriptor base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet_schema_descriptor_structure_from_iq,
    canonical_packet_schema_descriptor_structure_from_runs,
    packet_schema_descriptor_structure_from_bits.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet_schema_descriptor_fresh :
  forall descriptor state base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet_schema_descriptor_fresh_from_iq
      descriptor state window_pairs threshold xs =
      canonical_packet_schema_descriptor_fresh_from_runs
        descriptor state base_pattern.
Proof.
  intros descriptor state base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet_schema_descriptor_fresh_from_iq,
    canonical_packet_schema_descriptor_fresh_from_runs,
    packet_schema_descriptor_fresh_from_bits.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet_schema_descriptor_observation :
  forall descriptor state base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    packet_schema_descriptor_observation_from_iq
      descriptor state window_pairs threshold xs =
      packet_schema_descriptor_observation_from_runs
        descriptor state base_pattern.
Proof.
  intros descriptor state base_pattern window_pairs threshold xs Hmatch.
  unfold packet_schema_descriptor_observation_from_iq,
    packet_schema_descriptor_observation_from_runs.
  rewrite
    (observed_iq_matches_family_implies_packet_schema_descriptor_structure
       descriptor base_pattern window_pairs threshold xs Hmatch).
  rewrite
    (observed_iq_matches_family_implies_packet_schema_descriptor_fresh
       descriptor state base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_descriptor :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    family_descriptor_from_iq window_pairs threshold xs =
      tx_family_descriptor base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold family_descriptor_from_iq, tx_family_descriptor, family_descriptor_from_runs.
  rewrite Hmatch.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_semantic_tower :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    semantic_tower_from_iq window_pairs threshold xs =
      tx_family_semantic_tower base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold semantic_tower_from_iq, tx_family_semantic_tower, semantic_tower_from_runs.
  rewrite Hmatch.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_frame_word
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_packet24
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_field_view
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_frame_bits_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_frame_bits_from_iq.
  rewrite Hclasses.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_frame_bit_count_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    frame_bit_count_from_iq window_pairs1 threshold1 xs =
      frame_bit_count_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold frame_bit_count_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_frame_word_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_word_from_iq window_pairs1 threshold1 xs =
      canonical_frame_word_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_frame_word_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet24_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet24_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_field_view_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_field_view_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_field_view_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet24_field_view_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet_structure_invariant :
  forall spec window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_structure_view_from_iq spec window_pairs1 threshold1 xs =
      canonical_packet_structure_view_from_iq spec window_pairs2 threshold2 xs.
Proof.
  intros spec window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet_structure_view_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_counter_view_invariant :
  forall schema window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_field_counter_view_from_iq schema window_pairs1 threshold1 xs =
      canonical_field_counter_view_from_iq schema window_pairs2 threshold2 xs.
Proof.
  intros schema window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_field_counter_view_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet_schema_fresh_invariant :
  forall kind state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_schema_fresh_from_iq
      kind state window_pairs1 threshold1 xs =
      canonical_packet_schema_fresh_from_iq
        kind state window_pairs2 threshold2 xs.
Proof.
  intros kind state window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet_schema_fresh_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet_schema_descriptor_structure_invariant :
  forall descriptor window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_schema_descriptor_structure_from_iq
      descriptor window_pairs1 threshold1 xs =
      canonical_packet_schema_descriptor_structure_from_iq
        descriptor window_pairs2 threshold2 xs.
Proof.
  intros descriptor window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet_schema_descriptor_structure_from_iq,
    packet_schema_descriptor_structure_from_bits.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet_schema_descriptor_fresh_invariant :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_schema_descriptor_fresh_from_iq
      descriptor state window_pairs1 threshold1 xs =
      canonical_packet_schema_descriptor_fresh_from_iq
        descriptor state window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet_schema_descriptor_fresh_from_iq,
    packet_schema_descriptor_fresh_from_bits.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_schema_descriptor_observation_invariant :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    packet_schema_descriptor_observation_from_iq
      descriptor state window_pairs1 threshold1 xs =
      packet_schema_descriptor_observation_from_iq
        descriptor state window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold packet_schema_descriptor_observation_from_iq.
  rewrite
    (frame_bits_invariant_between_iq_regimes_implies_packet_schema_descriptor_structure_invariant
       descriptor window_pairs1 threshold1 window_pairs2 threshold2 xs).
  - rewrite
      (frame_bits_invariant_between_iq_regimes_implies_packet_schema_descriptor_fresh_invariant
         descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs).
    + reflexivity.
    + apply class_invariant_between_iq_regimes_implies_frame_bits_invariant.
      exact Hclasses.
  - apply class_invariant_between_iq_regimes_implies_frame_bits_invariant.
    exact Hclasses.
Qed.

Theorem class_invariant_between_iq_regimes_implies_frame_word_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_word_from_iq window_pairs1 threshold1 xs =
      canonical_frame_word_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_frame_word_from_iq.
  rewrite class_invariant_between_iq_regimes_implies_frame_bits_invariant
    with (window_pairs1 := window_pairs1)
         (threshold1 := threshold1)
         (window_pairs2 := window_pairs2)
         (threshold2 := threshold2)
         (xs := xs).
  - reflexivity.
  - exact Hclasses.
Qed.

Theorem class_invariant_between_iq_regimes_implies_frame_bit_count_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    frame_bit_count_from_iq window_pairs1 threshold1 xs =
      frame_bit_count_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  apply frame_bits_invariant_between_iq_regimes_implies_frame_bit_count_invariant.
  apply class_invariant_between_iq_regimes_implies_frame_bits_invariant.
  exact Hclasses.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet24_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet24_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_field_view_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_field_view_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_field_view_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet24_field_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_decoded_view_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    decoded_packet_view_from_iq window_pairs1 threshold1 xs =
      decoded_packet_view_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold decoded_packet_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_frame_word_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_packet24_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_field_view_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_structure_invariant :
  forall spec window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_structure_view_from_iq spec window_pairs1 threshold1 xs =
      canonical_packet_structure_view_from_iq spec window_pairs2 threshold2 xs.
Proof.
  intros spec window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet_structure_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_counter_view_invariant :
  forall schema window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_field_counter_view_from_iq schema window_pairs1 threshold1 xs =
      canonical_field_counter_view_from_iq schema window_pairs2 threshold2 xs.
Proof.
  intros schema window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_field_counter_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_descriptor_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    family_descriptor_from_iq window_pairs1 threshold1 xs =
      family_descriptor_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold family_descriptor_from_iq.
  rewrite Hclasses.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_semantic_tower_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    semantic_tower_from_iq window_pairs1 threshold1 xs =
      semantic_tower_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold semantic_tower_from_iq.
  rewrite Hclasses.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_frame_word_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_packet24_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_field_view_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_schema_descriptor_profile_invariant :
  forall descriptor window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    packet_schema_descriptor_profile_from_bits_sequence
      descriptor
      (frame_bits_sequence_from_iq window_pairs1 threshold1 xss) =
      packet_schema_descriptor_profile_from_bits_sequence
        descriptor
        (frame_bits_sequence_from_iq window_pairs2 threshold2 xss).
Proof.
  intros descriptor window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  apply frame_bits_sequence_invariant_between_iq_regimes_implies_packet_schema_descriptor_profile_invariant.
  exact Hbits.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_schema_descriptor_fresh_sequence_invariant :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xss,
    frame_bits_sequence_from_iq window_pairs1 threshold1 xss =
      frame_bits_sequence_from_iq window_pairs2 threshold2 xss ->
    canonical_packet_schema_descriptor_fresh_sequence_from_iq
      descriptor state window_pairs1 threshold1 xss =
      canonical_packet_schema_descriptor_fresh_sequence_from_iq
        descriptor state window_pairs2 threshold2 xss.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xss Hbits.
  apply frame_bits_sequence_invariant_between_iq_regimes_implies_packet_schema_descriptor_fresh_sequence_invariant.
  exact Hbits.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_schema_descriptor_phase_signature_invariant :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    packet_schema_descriptor_phase_signature_from_iq
      descriptor state window_pairs1 threshold1 xs =
      packet_schema_descriptor_phase_signature_from_iq
        descriptor state window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold packet_schema_descriptor_phase_signature_from_iq.
  rewrite Hclasses.
  rewrite
    (class_invariant_between_iq_regimes_implies_frame_bit_count_invariant
       window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite
    (class_invariant_between_iq_regimes_implies_decoded_view_invariant
       window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite
    (class_invariant_between_iq_regimes_implies_packet_schema_descriptor_observation_invariant
       descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Definition class_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  canonical_pulse_classes_from_iq window_pairs1 threshold1 xs <>
    canonical_pulse_classes_from_iq window_pairs2 threshold2 xs.

Definition frame_bit_count_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  frame_bit_count_from_iq window_pairs1 threshold1 xs <>
    frame_bit_count_from_iq window_pairs2 threshold2 xs.

Definition frame_word_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  canonical_frame_word_from_iq window_pairs1 threshold1 xs <>
    canonical_frame_word_from_iq window_pairs2 threshold2 xs.

Definition decoded_view_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  decoded_packet_view_from_iq window_pairs1 threshold1 xs <>
    decoded_packet_view_from_iq window_pairs2 threshold2 xs.

Definition family_descriptor_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  family_descriptor_from_iq window_pairs1 threshold1 xs <>
    family_descriptor_from_iq window_pairs2 threshold2 xs.

Definition semantic_tower_transition_between_iq_regimes
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  semantic_tower_from_iq window_pairs1 threshold1 xs <>
    semantic_tower_from_iq window_pairs2 threshold2 xs.

Definition packet_schema_descriptor_observation_transition_between_iq_regimes
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  packet_schema_descriptor_observation_from_iq
    descriptor state window_pairs1 threshold1 xs <>
  packet_schema_descriptor_observation_from_iq
    descriptor state window_pairs2 threshold2 xs.

Definition packet_schema_descriptor_phase_transition_between_iq_regimes
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : Prop :=
  packet_schema_descriptor_phase_signature_from_iq
    descriptor state window_pairs1 threshold1 xs <>
  packet_schema_descriptor_phase_signature_from_iq
    descriptor state window_pairs2 threshold2 xs.

Record ObservationRegime := {
  regime_window_pairs : nat;
  regime_threshold : nat
}.

Definition observation_regime_eqb
    (x y : ObservationRegime)
    : bool :=
  Nat.eqb (regime_window_pairs x) (regime_window_pairs y)
  &&
  Nat.eqb (regime_threshold x) (regime_threshold y).

Definition class_signature_from_iq_regime
    (regime : ObservationRegime)
    (xs : ByteStream)
    : CanonicalRFObject :=
  canonical_pulse_classes_from_iq
    (regime_window_pairs regime)
    (regime_threshold regime)
    xs.

Definition frame_bit_count_from_iq_regime
    (regime : ObservationRegime)
    (xs : ByteStream)
    : nat :=
  frame_bit_count_from_iq
    (regime_window_pairs regime)
    (regime_threshold regime)
    xs.

Definition decoded_view_from_iq_regime
    (regime : ObservationRegime)
    (xs : ByteStream)
    : DecodedPacketView :=
  decoded_packet_view_from_iq
    (regime_window_pairs regime)
    (regime_threshold regime)
    xs.

Definition packet_schema_descriptor_phase_signature_from_iq_regime
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (regime : ObservationRegime)
    (xs : ByteStream)
    : PacketSchemaDescriptorPhaseSignature :=
  packet_schema_descriptor_phase_signature_from_iq
    descriptor state
    (regime_window_pairs regime)
    (regime_threshold regime)
    xs.

Definition class_transition_between_observation_regimes
    (regime1 regime2 : ObservationRegime)
    (xs : ByteStream)
    : Prop :=
  class_signature_from_iq_regime regime1 xs <>
    class_signature_from_iq_regime regime2 xs.

Definition packet_schema_descriptor_phase_transition_between_observation_regimes
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (regime1 regime2 : ObservationRegime)
    (xs : ByteStream)
    : Prop :=
  packet_schema_descriptor_phase_signature_from_iq_regime
    descriptor state regime1 xs <>
  packet_schema_descriptor_phase_signature_from_iq_regime
    descriptor state regime2 xs.

Fixpoint last_observation_regime_or
    (default : ObservationRegime)
    (rs : list ObservationRegime)
    : ObservationRegime :=
  match rs with
  | [] => default
  | r :: rs' => last_observation_regime_or r rs'
  end.

Fixpoint regime_path_class_stable
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : Prop :=
  match rs with
  | [] => True
  | r1 :: rs' =>
      match rs' with
      | [] => True
      | r2 :: _ =>
          class_signature_from_iq_regime r1 xs =
            class_signature_from_iq_regime r2 xs /\
          regime_path_class_stable xs rs'
      end
  end.

Fixpoint regime_path_phase_stable
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : Prop :=
  match rs with
  | [] => True
  | r1 :: rs' =>
      match rs' with
      | [] => True
      | r2 :: _ =>
          packet_schema_descriptor_phase_signature_from_iq_regime
            descriptor state r1 xs =
            packet_schema_descriptor_phase_signature_from_iq_regime
              descriptor state r2 xs /\
          regime_path_phase_stable descriptor state xs rs'
      end
  end.

Definition class_transition_between_iq_regimesb
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : bool :=
  negb
    (pulse_class_list_eqb
       (canonical_pulse_classes_from_iq window_pairs1 threshold1 xs)
       (canonical_pulse_classes_from_iq window_pairs2 threshold2 xs)).

Definition packet_schema_descriptor_phase_transition_between_iq_regimesb
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (window_pairs1 threshold1 window_pairs2 threshold2 : nat)
    (xs : ByteStream)
    : bool :=
  negb
    (packet_schema_descriptor_phase_signature_eqb
       (packet_schema_descriptor_phase_signature_from_iq
          descriptor state window_pairs1 threshold1 xs)
       (packet_schema_descriptor_phase_signature_from_iq
          descriptor state window_pairs2 threshold2 xs)).

Definition class_transition_between_observation_regimesb
    (regime1 regime2 : ObservationRegime)
    (xs : ByteStream)
    : bool :=
  negb
    (pulse_class_list_eqb
       (class_signature_from_iq_regime regime1 xs)
       (class_signature_from_iq_regime regime2 xs)).

Definition packet_schema_descriptor_phase_transition_between_observation_regimesb
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (regime1 regime2 : ObservationRegime)
    (xs : ByteStream)
    : bool :=
  negb
    (packet_schema_descriptor_phase_signature_eqb
       (packet_schema_descriptor_phase_signature_from_iq_regime
          descriptor state regime1 xs)
       (packet_schema_descriptor_phase_signature_from_iq_regime
          descriptor state regime2 xs)).

Fixpoint regime_path_class_stableb
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : bool :=
  match rs with
  | [] => true
  | r1 :: rs' =>
      match rs' with
      | [] => true
      | r2 :: _ =>
          pulse_class_list_eqb
            (class_signature_from_iq_regime r1 xs)
            (class_signature_from_iq_regime r2 xs)
          &&
          regime_path_class_stableb xs rs'
      end
  end.

Fixpoint regime_path_phase_stableb
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : bool :=
  match rs with
  | [] => true
  | r1 :: rs' =>
      match rs' with
      | [] => true
      | r2 :: _ =>
          packet_schema_descriptor_phase_signature_eqb
            (packet_schema_descriptor_phase_signature_from_iq_regime
               descriptor state r1 xs)
            (packet_schema_descriptor_phase_signature_from_iq_regime
               descriptor state r2 xs)
          &&
          regime_path_phase_stableb descriptor state xs rs'
      end
  end.

Fixpoint regime_path_has_class_transitionb
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : bool :=
  match rs with
  | [] => false
  | r1 :: rs' =>
      match rs' with
      | [] => false
      | r2 :: _ =>
          class_transition_between_observation_regimesb r1 r2 xs
          ||
          regime_path_has_class_transitionb xs rs'
      end
  end.

Fixpoint regime_path_has_phase_transitionb
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : bool :=
  match rs with
  | [] => false
  | r1 :: rs' =>
      match rs' with
      | [] => false
      | r2 :: _ =>
          packet_schema_descriptor_phase_transition_between_observation_regimesb
            descriptor state r1 r2 xs
          ||
          regime_path_has_phase_transitionb descriptor state xs rs'
      end
  end.

Definition phase_signature_sequence_from_iq_regimes
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (rs : list ObservationRegime)
    (xs : ByteStream)
    : list PacketSchemaDescriptorPhaseSignature :=
  map
    (fun regime =>
       packet_schema_descriptor_phase_signature_from_iq_regime
         descriptor state regime xs)
    rs.

Fixpoint observation_regime_class_transition_mask
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : list bool :=
  match rs with
  | [] => []
  | r1 :: rs' =>
      match rs' with
      | [] => []
      | r2 :: _ =>
          class_transition_between_observation_regimesb r1 r2 xs
          :: observation_regime_class_transition_mask xs rs'
      end
  end.

Fixpoint observation_regime_phase_transition_mask
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (xs : ByteStream)
    (rs : list ObservationRegime)
    : list bool :=
  match rs with
  | [] => []
  | r1 :: rs' =>
      match rs' with
      | [] => []
      | r2 :: _ =>
          packet_schema_descriptor_phase_transition_between_observation_regimesb
            descriptor state r1 r2 xs
          :: observation_regime_phase_transition_mask descriptor state xs rs'
      end
  end.

Record RegimePhaseAtlas := {
  atlas_regimes : list ObservationRegime;
  atlas_phase_signatures : list PacketSchemaDescriptorPhaseSignature;
  atlas_class_transition_mask : list bool;
  atlas_phase_transition_mask : list bool;
  atlas_class_stable : bool;
  atlas_phase_stable : bool
}.

Definition regime_phase_atlas_from_iq
    (descriptor : PacketSchemaDescriptor)
    (state : PacketSchemaState)
    (rs : list ObservationRegime)
    (xs : ByteStream)
    : RegimePhaseAtlas :=
  {| atlas_regimes := rs;
     atlas_phase_signatures :=
       phase_signature_sequence_from_iq_regimes descriptor state rs xs;
     atlas_class_transition_mask :=
       observation_regime_class_transition_mask xs rs;
     atlas_phase_transition_mask :=
       observation_regime_phase_transition_mask descriptor state xs rs;
     atlas_class_stable := regime_path_class_stableb xs rs;
     atlas_phase_stable := regime_path_phase_stableb descriptor state xs rs |}.

Lemma pulse_class_eqb_true_iff :
  forall x y,
    pulse_class_eqb x y = true <-> x = y.
Proof.
  intros x y.
  destruct x, y; simpl; split; intro H; try discriminate; reflexivity.
Qed.

Lemma pulse_class_list_eqb_true_iff :
  forall xs ys,
    pulse_class_list_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - destruct ys as [|y ys]; simpl; split; intro H; try discriminate; reflexivity.
  - destruct ys as [|y ys]; simpl.
    + split.
      * intro H.
        discriminate.
      * intro H.
        inversion H.
    + split.
      * intro H.
        apply Bool.andb_true_iff in H as [Hxy Hrest].
        apply pulse_class_eqb_true_iff in Hxy.
        apply IH in Hrest.
        subst.
        reflexivity.
      * intro H.
        inversion H; subst.
        apply Bool.andb_true_iff.
        split.
        -- apply pulse_class_eqb_true_iff.
           reflexivity.
        -- apply IH.
           reflexivity.
Qed.

Lemma bool_list_eqb_true_iff :
  forall xs ys,
    bool_list_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - destruct ys as [|y ys]; simpl; split; intro H; try discriminate; reflexivity.
  - destruct ys as [|y ys]; simpl.
    + split.
      * intro H.
        discriminate.
      * intro H.
        inversion H.
    + split.
      * intro H.
        apply Bool.andb_true_iff in H as [Hxy Hrest].
        destruct x, y; simpl in Hxy; try discriminate;
          apply IH in Hrest; subst; reflexivity.
      * intro H.
        inversion H; subst.
        apply Bool.andb_true_iff.
        split.
        -- destruct y; reflexivity.
        -- apply IH.
           reflexivity.
Qed.

Lemma packet24_eqb_true_iff :
  forall x y,
    packet24_eqb x y = true <-> x = y.
Proof.
  intros [xh xm xl] [yh ym yl]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hxy Hz].
    apply Bool.andb_true_iff in Hxy as [Hh Hm].
    apply Nat.eqb_eq in Hh.
    apply Nat.eqb_eq in Hm.
    apply Nat.eqb_eq in Hz.
    cbn in Hh, Hm, Hz.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    cbn.
    apply Bool.andb_true_iff.
    split.
    + apply Bool.andb_true_iff.
      split.
      * apply Nat.eqb_eq.
        reflexivity.
      * apply Nat.eqb_eq.
        reflexivity.
    + apply Nat.eqb_eq.
      reflexivity.
Qed.

Lemma packet24_byte_view_eqb_true_iff :
  forall x y,
    packet24_byte_view_eqb x y = true <-> x = y.
Proof.
  intros [x0 x1 x2] [y0 y1 y2]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hxy Hz].
    apply Bool.andb_true_iff in Hxy as [H0 H1].
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in Hz.
    cbn in H0, H1, Hz.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    cbn.
    apply Bool.andb_true_iff.
    split.
    + apply Bool.andb_true_iff.
      split.
      * apply Nat.eqb_eq.
        reflexivity.
      * apply Nat.eqb_eq.
        reflexivity.
    + apply Nat.eqb_eq.
      reflexivity.
Qed.

Lemma packet24_nibble_view_eqb_true_iff :
  forall x y,
    packet24_nibble_view_eqb x y = true <-> x = y.
Proof.
  intros [x0 x1 x2 x3 x4 x5] [y0 y1 y2 y3 y4 y5]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [H01234 H5].
    apply Bool.andb_true_iff in H01234 as [H0123 H4].
    apply Bool.andb_true_iff in H0123 as [H012 H3].
    apply Bool.andb_true_iff in H012 as [H01 H2].
    apply Bool.andb_true_iff in H01 as [H0 H1].
    apply Nat.eqb_eq in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2.
    apply Nat.eqb_eq in H3.
    apply Nat.eqb_eq in H4.
    apply Nat.eqb_eq in H5.
    cbn in H0, H1, H2, H3, H4, H5.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    unfold packet24_nibble_view_eqb.
    cbn.
    repeat rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Lemma packet24_field_view_eqb_true_iff :
  forall x y,
    packet24_field_view_eqb x y = true <-> x = y.
Proof.
  intros [xb xn xp xs] [yb yn yp ys]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hbytes_nibbles_prefix Hsuffix].
    apply Bool.andb_true_iff in Hbytes_nibbles_prefix as [Hbytes_nibbles Hprefix].
    apply Bool.andb_true_iff in Hbytes_nibbles as [Hbytes Hnibbles].
    apply packet24_byte_view_eqb_true_iff in Hbytes.
    apply packet24_nibble_view_eqb_true_iff in Hnibbles.
    apply Nat.eqb_eq in Hprefix.
    apply Nat.eqb_eq in Hsuffix.
    cbn in Hbytes, Hnibbles, Hprefix, Hsuffix.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    unfold packet24_field_view_eqb.
    cbn.
    rewrite (proj2 (packet24_byte_view_eqb_true_iff yb yb) eq_refl).
    rewrite (proj2 (packet24_nibble_view_eqb_true_iff yn yn) eq_refl).
    repeat rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Lemma packet_structured_field_value_eqb_true_iff :
  forall x y,
    packet_structured_field_value_eqb x y = true <-> x = y.
Proof.
  intros [xr xo xw xv] [yr yo yw yv]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hrole_offset_width Hvalue].
    apply Bool.andb_true_iff in Hrole_offset_width as [Hrole_offset Hwidth].
    apply Bool.andb_true_iff in Hrole_offset as [Hrole Hoffset].
    apply Nat.eqb_eq in Hrole.
    apply Nat.eqb_eq in Hoffset.
    apply Nat.eqb_eq in Hwidth.
    apply Nat.eqb_eq in Hvalue.
    cbn in Hrole, Hoffset, Hwidth, Hvalue.
    destruct xr, yr; simpl in Hrole; try discriminate; subst; subst; reflexivity.
  - intro H.
    inversion H; subst.
    unfold packet_structured_field_value_eqb.
    cbn.
    repeat rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Lemma packet_structured_field_value_list_eqb_true_iff :
  forall xs ys,
    packet_structured_field_value_list_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - destruct ys as [|y ys]; simpl; split; intro H; try discriminate; reflexivity.
  - destruct ys as [|y ys]; simpl.
    + split.
      * intro H.
        discriminate.
      * intro H.
        inversion H.
    + split.
      * intro H.
        apply Bool.andb_true_iff in H as [Hxy Hrest].
        apply packet_structured_field_value_eqb_true_iff in Hxy.
        apply IH in Hrest.
        subst.
        reflexivity.
      * intro H.
        inversion H; subst.
        apply Bool.andb_true_iff.
        split.
        -- apply packet_structured_field_value_eqb_true_iff.
           reflexivity.
        -- apply IH.
           reflexivity.
Qed.

Lemma packet_schema_descriptor_observation_eqb_true_iff :
  forall x y,
    packet_schema_descriptor_observation_eqb x y = true <-> x = y.
Proof.
  intros [xs xf] [ys yf]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hstructure Hfresh].
    apply packet_structured_field_value_list_eqb_true_iff in Hstructure.
    destruct xf, yf; simpl in Hfresh; try discriminate;
      cbn in Hstructure; subst; reflexivity.
  - intro H.
    inversion H; subst.
    cbn.
    apply Bool.andb_true_iff.
    split.
    + apply packet_structured_field_value_list_eqb_true_iff.
      reflexivity.
    + destruct yf; reflexivity.
Qed.

Lemma decoded_packet_view_eqb_true_iff :
  forall x y,
    decoded_packet_view_eqb x y = true <-> x = y.
Proof.
  intros [xb xw xp xf] [yb yw yp yf]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hbits_word_packet Hfields].
    apply Bool.andb_true_iff in Hbits_word_packet as [Hbits_word Hpacket].
    apply Bool.andb_true_iff in Hbits_word as [Hbits Hword].
    apply bool_list_eqb_true_iff in Hbits.
    apply Nat.eqb_eq in Hword.
    apply packet24_eqb_true_iff in Hpacket.
    apply packet24_field_view_eqb_true_iff in Hfields.
    cbn in Hbits, Hword, Hpacket, Hfields.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    unfold decoded_packet_view_eqb.
    cbn.
    rewrite (proj2 (bool_list_eqb_true_iff yb yb) eq_refl).
    rewrite Nat.eqb_refl.
    rewrite (proj2 (packet24_eqb_true_iff yp yp) eq_refl).
    rewrite (proj2 (packet24_field_view_eqb_true_iff yf yf) eq_refl).
    reflexivity.
Qed.

Lemma packet_schema_descriptor_phase_signature_eqb_true_iff :
  forall x y,
    packet_schema_descriptor_phase_signature_eqb x y = true <-> x = y.
Proof.
  intros [xo xc xv xs] [yo yc yv ys]; simpl.
  split.
  - intro H.
    apply Bool.andb_true_iff in H as [Hobj_count_view Hschema].
    apply Bool.andb_true_iff in Hobj_count_view as [Hobj_count Hview].
    apply Bool.andb_true_iff in Hobj_count as [Hobj Hcount].
    apply pulse_class_list_eqb_true_iff in Hobj.
    apply Nat.eqb_eq in Hcount.
    apply decoded_packet_view_eqb_true_iff in Hview.
    apply packet_schema_descriptor_observation_eqb_true_iff in Hschema.
    cbn in Hobj, Hcount, Hview, Hschema.
    subst.
    reflexivity.
  - intro H.
    inversion H; subst.
    unfold packet_schema_descriptor_phase_signature_eqb.
    cbn.
    rewrite (proj2 (pulse_class_list_eqb_true_iff yo yo) eq_refl).
    rewrite Nat.eqb_refl.
    rewrite (proj2 (decoded_packet_view_eqb_true_iff yv yv) eq_refl).
    rewrite (proj2 (packet_schema_descriptor_observation_eqb_true_iff ys ys) eq_refl).
    reflexivity.
Qed.

Lemma regime_path_class_stableb_true_iff :
  forall xs rs,
    regime_path_class_stableb xs rs = true <->
    regime_path_class_stable xs rs.
Proof.
  intros xs rs.
  induction rs as [|r1 rs' IH]; simpl.
  - split.
    + intro H.
      exact I.
    + intro H.
      reflexivity.
  - destruct rs' as [|r2 rs'']; simpl.
    + split.
      * intro H.
        exact I.
      * intro H.
        reflexivity.
    + split.
      * intro H.
        apply Bool.andb_true_iff in H as [H12 Hrest].
        split.
        -- apply pulse_class_list_eqb_true_iff in H12.
           exact H12.
        -- apply IH in Hrest.
           exact Hrest.
      * intro H.
        destruct H as [H12 Hrest].
        apply Bool.andb_true_iff.
        split.
        -- apply pulse_class_list_eqb_true_iff.
           exact H12.
        -- apply IH.
           exact Hrest.
Qed.

Lemma regime_path_phase_stableb_true_iff :
  forall descriptor state xs rs,
    regime_path_phase_stableb descriptor state xs rs = true <->
    regime_path_phase_stable descriptor state xs rs.
Proof.
  intros descriptor state xs rs.
  induction rs as [|r1 rs' IH]; simpl.
  - split.
    + intro H.
      exact I.
    + intro H.
      reflexivity.
  - destruct rs' as [|r2 rs'']; simpl.
    + split.
      * intro H.
        exact I.
      * intro H.
        reflexivity.
    + split.
      * intro H.
        apply Bool.andb_true_iff in H as [H12 Hrest].
        split.
        -- apply packet_schema_descriptor_phase_signature_eqb_true_iff in H12.
           exact H12.
        -- apply IH in Hrest.
           exact Hrest.
      * intro H.
        destruct H as [H12 Hrest].
        apply Bool.andb_true_iff.
        split.
        -- apply packet_schema_descriptor_phase_signature_eqb_true_iff.
           exact H12.
        -- apply IH.
           exact Hrest.
Qed.

Theorem regime_path_has_class_transitionb_eq_negb_regime_path_class_stableb :
  forall xs rs,
    regime_path_has_class_transitionb xs rs =
      negb (regime_path_class_stableb xs rs).
Proof.
  intros xs rs.
  induction rs as [|r1 rs' IH]; simpl.
  - reflexivity.
  - destruct rs' as [|r2 rs'']; simpl.
    + reflexivity.
    + unfold class_transition_between_observation_regimesb.
      destruct (pulse_class_list_eqb
                  (class_signature_from_iq_regime r1 xs)
                  (class_signature_from_iq_regime r2 xs)) eqn:Heq; simpl.
      * exact IH.
      * reflexivity.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_observation_regimes_implies_class_transition :
  forall descriptor state regime1 regime2 xs,
    packet_schema_descriptor_phase_transition_between_observation_regimes
      descriptor state regime1 regime2 xs ->
    class_transition_between_observation_regimes
      regime1 regime2 xs.
Proof.
  intros descriptor state regime1 regime2 xs Hphase Hclasses.
  unfold packet_schema_descriptor_phase_transition_between_observation_regimes in Hphase.
  unfold class_transition_between_observation_regimes in Hclasses.
  unfold packet_schema_descriptor_phase_signature_from_iq_regime,
    class_signature_from_iq_regime in *.
  apply Hphase.
  apply class_invariant_between_iq_regimes_implies_packet_schema_descriptor_phase_signature_invariant.
  exact Hclasses.
Qed.

Theorem frame_bit_count_transition_between_iq_regimes_implies_class_transition :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    frame_bit_count_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hcount Hclasses.
  apply Hcount.
  apply class_invariant_between_iq_regimes_implies_frame_bit_count_invariant.
  exact Hclasses.
Qed.

Theorem frame_word_transition_between_iq_regimes_implies_class_transition :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    frame_word_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hword Hclasses.
  apply Hword.
  apply class_invariant_between_iq_regimes_implies_frame_word_invariant.
  exact Hclasses.
Qed.

Theorem decoded_view_transition_between_iq_regimes_implies_class_transition :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    decoded_view_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hview Hclasses.
  apply Hview.
  apply class_invariant_between_iq_regimes_implies_decoded_view_invariant.
  exact Hclasses.
Qed.

Theorem family_descriptor_transition_between_iq_regimes_implies_class_transition :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    family_descriptor_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hdescriptor Hclasses.
  apply Hdescriptor.
  apply class_invariant_between_iq_regimes_implies_descriptor_invariant.
  exact Hclasses.
Qed.

Theorem semantic_tower_transition_between_iq_regimes_implies_class_transition :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    semantic_tower_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Htower Hclasses.
  apply Htower.
  apply class_invariant_between_iq_regimes_implies_semantic_tower_invariant.
  exact Hclasses.
Qed.

Theorem packet_schema_descriptor_observation_transition_between_iq_regimes_implies_class_transition :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    packet_schema_descriptor_observation_transition_between_iq_regimes
      descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs
    Hobservation Hclasses.
  apply Hobservation.
  apply class_invariant_between_iq_regimes_implies_packet_schema_descriptor_observation_invariant.
  exact Hclasses.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_iq_regimes_implies_class_transition :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    packet_schema_descriptor_phase_transition_between_iq_regimes
      descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs ->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs
    Hphase Hclasses.
  apply Hphase.
  apply class_invariant_between_iq_regimes_implies_packet_schema_descriptor_phase_signature_invariant.
  exact Hclasses.
Qed.

Theorem class_invariant_between_observation_regimes_implies_phase_signature_invariant :
  forall descriptor state regime1 regime2 xs,
    class_signature_from_iq_regime regime1 xs =
      class_signature_from_iq_regime regime2 xs ->
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state regime1 xs =
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state regime2 xs.
Proof.
  intros descriptor state regime1 regime2 xs Hclasses.
  unfold class_signature_from_iq_regime,
    packet_schema_descriptor_phase_signature_from_iq_regime in *.
  apply class_invariant_between_iq_regimes_implies_packet_schema_descriptor_phase_signature_invariant.
  exact Hclasses.
Qed.

Theorem regime_path_class_stable_implies_phase_stable :
  forall descriptor state xs rs,
    regime_path_class_stable xs rs ->
    regime_path_phase_stable descriptor state xs rs.
Proof.
  intros descriptor state xs rs.
  induction rs as [|r1 rs' IH]; simpl; intro Hstable.
  - exact I.
  - destruct rs' as [|r2 rs'']; simpl in *.
    + exact I.
    + destruct Hstable as [H12 Hrest].
      split.
      * apply class_invariant_between_observation_regimes_implies_phase_signature_invariant.
        exact H12.
      * apply IH.
        exact Hrest.
Qed.

Theorem regime_path_phase_stable_implies_endpoint_phase_invariant :
  forall descriptor state xs r rs,
    regime_path_phase_stable descriptor state xs (r :: rs) ->
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs =
      packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state (last_observation_regime_or r rs) xs.
Proof.
  intros descriptor state xs r rs.
  revert r.
  induction rs as [|r2 rs' IH]; intros r Hstable; simpl in *.
  - reflexivity.
  - destruct rs' as [|r3 rs'']; simpl in *.
    + destruct Hstable as [H12 _].
      exact H12.
    + destruct Hstable as [H12 Hrest].
      rewrite H12.
      apply (IH r2).
      exact Hrest.
Qed.

Theorem regime_path_class_stable_implies_endpoint_phase_invariant :
  forall descriptor state xs r rs,
    regime_path_class_stable xs (r :: rs) ->
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs =
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs.
Proof.
  intros descriptor state xs r rs Hstable.
  apply regime_path_phase_stable_implies_endpoint_phase_invariant.
  apply regime_path_class_stable_implies_phase_stable.
  exact Hstable.
Qed.

Theorem endpoint_phase_transition_implies_not_regime_path_class_stable :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    ~ regime_path_class_stable xs (r :: rs).
Proof.
  intros descriptor state xs r rs Htransition Hstable.
  apply Htransition.
  apply regime_path_class_stable_implies_endpoint_phase_invariant.
  exact Hstable.
Qed.

Theorem regime_path_has_phase_transitionb_eq_negb_regime_path_phase_stableb :
  forall descriptor state xs rs,
    regime_path_has_phase_transitionb descriptor state xs rs =
      negb (regime_path_phase_stableb descriptor state xs rs).
Proof.
  intros descriptor state xs rs.
  induction rs as [|r1 rs' IH]; simpl.
  - reflexivity.
  - destruct rs' as [|r2 rs'']; simpl.
    + reflexivity.
    + unfold packet_schema_descriptor_phase_transition_between_observation_regimesb.
      destruct (packet_schema_descriptor_phase_signature_eqb
                  (packet_schema_descriptor_phase_signature_from_iq_regime
                     descriptor state r1 xs)
                  (packet_schema_descriptor_phase_signature_from_iq_regime
                     descriptor state r2 xs)) eqn:Heq; simpl.
      * exact IH.
      * reflexivity.
Qed.

Theorem class_transition_between_iq_regimesb_true_iff :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    class_transition_between_iq_regimesb
      window_pairs1 threshold1 window_pairs2 threshold2 xs = true <->
    class_transition_between_iq_regimes
      window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs.
  split.
  - intros Htransition Heq.
    unfold class_transition_between_iq_regimesb in Htransition.
    apply Bool.negb_true_iff in Htransition.
    assert
      (pulse_class_list_eqb
         (canonical_pulse_classes_from_iq window_pairs1 threshold1 xs)
         (canonical_pulse_classes_from_iq window_pairs2 threshold2 xs) = true)
      as Heqb.
    { apply pulse_class_list_eqb_true_iff.
      exact Heq. }
    rewrite Heqb in Htransition.
    discriminate.
  - intro Htransition.
    unfold class_transition_between_iq_regimesb.
    destruct (pulse_class_list_eqb
                (canonical_pulse_classes_from_iq window_pairs1 threshold1 xs)
                (canonical_pulse_classes_from_iq window_pairs2 threshold2 xs))
      eqn:Heqb.
    + exfalso.
      apply Htransition.
      apply pulse_class_list_eqb_true_iff.
      exact Heqb.
    + reflexivity.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_iq_regimesb_true_iff :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    packet_schema_descriptor_phase_transition_between_iq_regimesb
      descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs = true <->
    packet_schema_descriptor_phase_transition_between_iq_regimes
      descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs.
  split.
  - intros Htransition Heq.
    unfold packet_schema_descriptor_phase_transition_between_iq_regimesb in Htransition.
    apply Bool.negb_true_iff in Htransition.
    assert
      (packet_schema_descriptor_phase_signature_eqb
         (packet_schema_descriptor_phase_signature_from_iq
            descriptor state window_pairs1 threshold1 xs)
         (packet_schema_descriptor_phase_signature_from_iq
            descriptor state window_pairs2 threshold2 xs) = true)
      as Heqb.
    { apply packet_schema_descriptor_phase_signature_eqb_true_iff.
      exact Heq. }
    rewrite Heqb in Htransition.
    discriminate.
  - intro Htransition.
    unfold packet_schema_descriptor_phase_transition_between_iq_regimesb.
    destruct (packet_schema_descriptor_phase_signature_eqb
                (packet_schema_descriptor_phase_signature_from_iq
                   descriptor state window_pairs1 threshold1 xs)
                (packet_schema_descriptor_phase_signature_from_iq
                   descriptor state window_pairs2 threshold2 xs))
      eqn:Heqb.
    + exfalso.
      apply Htransition.
      apply packet_schema_descriptor_phase_signature_eqb_true_iff.
      exact Heqb.
    + reflexivity.
Qed.

Theorem class_transition_between_observation_regimesb_true_iff :
  forall regime1 regime2 xs,
    class_transition_between_observation_regimesb regime1 regime2 xs = true <->
    class_transition_between_observation_regimes regime1 regime2 xs.
Proof.
  intros regime1 regime2 xs.
  split.
  - intros Htransition Heq.
    unfold class_transition_between_observation_regimesb in Htransition.
    apply Bool.negb_true_iff in Htransition.
    assert
      (pulse_class_list_eqb
         (class_signature_from_iq_regime regime1 xs)
         (class_signature_from_iq_regime regime2 xs) = true)
      as Heqb.
    { apply pulse_class_list_eqb_true_iff.
      exact Heq. }
    rewrite Heqb in Htransition.
    discriminate.
  - intro Htransition.
    unfold class_transition_between_observation_regimesb.
    destruct (pulse_class_list_eqb
                (class_signature_from_iq_regime regime1 xs)
                (class_signature_from_iq_regime regime2 xs))
      eqn:Heqb.
    + exfalso.
      apply Htransition.
      apply pulse_class_list_eqb_true_iff.
      exact Heqb.
    + reflexivity.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_observation_regimesb_true_iff :
  forall descriptor state regime1 regime2 xs,
    packet_schema_descriptor_phase_transition_between_observation_regimesb
      descriptor state regime1 regime2 xs = true <->
    packet_schema_descriptor_phase_transition_between_observation_regimes
      descriptor state regime1 regime2 xs.
Proof.
  intros descriptor state regime1 regime2 xs.
  split.
  - intros Htransition Heq.
    unfold packet_schema_descriptor_phase_transition_between_observation_regimesb in Htransition.
    apply Bool.negb_true_iff in Htransition.
    assert
      (packet_schema_descriptor_phase_signature_eqb
         (packet_schema_descriptor_phase_signature_from_iq_regime
            descriptor state regime1 xs)
         (packet_schema_descriptor_phase_signature_from_iq_regime
            descriptor state regime2 xs) = true)
      as Heqb.
    { apply packet_schema_descriptor_phase_signature_eqb_true_iff.
      exact Heq. }
    rewrite Heqb in Htransition.
    discriminate.
  - intro Htransition.
    unfold packet_schema_descriptor_phase_transition_between_observation_regimesb.
    destruct (packet_schema_descriptor_phase_signature_eqb
                (packet_schema_descriptor_phase_signature_from_iq_regime
                   descriptor state regime1 xs)
                (packet_schema_descriptor_phase_signature_from_iq_regime
                   descriptor state regime2 xs))
      eqn:Heqb.
    + exfalso.
      apply Htransition.
      apply packet_schema_descriptor_phase_signature_eqb_true_iff.
      exact Heqb.
    + reflexivity.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_iq_regimesb_true_implies_class_transition_between_iq_regimesb_true :
  forall descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs,
    packet_schema_descriptor_phase_transition_between_iq_regimesb
      descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs = true ->
    class_transition_between_iq_regimesb
      window_pairs1 threshold1 window_pairs2 threshold2 xs = true.
Proof.
  intros descriptor state window_pairs1 threshold1 window_pairs2 threshold2 xs
    Hphase.
  apply class_transition_between_iq_regimesb_true_iff.
  eapply packet_schema_descriptor_phase_transition_between_iq_regimes_implies_class_transition.
  apply packet_schema_descriptor_phase_transition_between_iq_regimesb_true_iff.
  exact Hphase.
Qed.

Theorem packet_schema_descriptor_phase_transition_between_observation_regimesb_true_implies_class_transition_between_observation_regimesb_true :
  forall descriptor state regime1 regime2 xs,
    packet_schema_descriptor_phase_transition_between_observation_regimesb
      descriptor state regime1 regime2 xs = true ->
    class_transition_between_observation_regimesb regime1 regime2 xs = true.
Proof.
  intros descriptor state regime1 regime2 xs Hphase.
  apply class_transition_between_observation_regimesb_true_iff.
  eapply packet_schema_descriptor_phase_transition_between_observation_regimes_implies_class_transition.
  apply packet_schema_descriptor_phase_transition_between_observation_regimesb_true_iff.
  exact Hphase.
Qed.

Theorem regime_path_has_phase_transitionb_true_implies_regime_path_has_class_transitionb_true :
  forall descriptor state xs rs,
    regime_path_has_phase_transitionb descriptor state xs rs = true ->
    regime_path_has_class_transitionb xs rs = true.
Proof.
  intros descriptor state xs rs Hphase.
  destruct (regime_path_has_class_transitionb xs rs) eqn:Hclass.
  - reflexivity.
  - rewrite regime_path_has_class_transitionb_eq_negb_regime_path_class_stableb in Hclass.
    apply Bool.negb_false_iff in Hclass.
    pose proof
      (proj1 (regime_path_class_stableb_true_iff xs rs) Hclass)
      as Hstable.
    pose proof
      (regime_path_class_stable_implies_phase_stable
         descriptor state xs rs Hstable)
      as Hphase_stable.
    pose proof
      (proj2 (regime_path_phase_stableb_true_iff descriptor state xs rs)
         Hphase_stable)
      as Hphaseb.
    rewrite regime_path_has_phase_transitionb_eq_negb_regime_path_phase_stableb in Hphase.
    rewrite Hphaseb in Hphase.
    discriminate.
Qed.

Theorem endpoint_phase_transition_implies_regime_path_phase_stableb_false :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    regime_path_phase_stableb descriptor state xs (r :: rs) = false.
Proof.
  intros descriptor state xs r rs Htransition.
  destruct (regime_path_phase_stableb descriptor state xs (r :: rs)) eqn:Hstable.
  - exfalso.
    apply Htransition.
    apply regime_path_phase_stable_implies_endpoint_phase_invariant.
    apply (proj1 (regime_path_phase_stableb_true_iff descriptor state xs (r :: rs))).
    exact Hstable.
  - reflexivity.
Qed.

Theorem endpoint_phase_transition_implies_regime_path_class_stableb_false :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    regime_path_class_stableb xs (r :: rs) = false.
Proof.
  intros descriptor state xs r rs Htransition.
  destruct (regime_path_class_stableb xs (r :: rs)) eqn:Hstable.
  - exfalso.
    apply Htransition.
    apply regime_path_class_stable_implies_endpoint_phase_invariant.
    apply (proj1 (regime_path_class_stableb_true_iff xs (r :: rs))).
    exact Hstable.
  - reflexivity.
Qed.

Theorem endpoint_phase_transition_implies_regime_path_has_phase_transitionb_true :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    regime_path_has_phase_transitionb descriptor state xs (r :: rs) = true.
Proof.
  intros descriptor state xs r rs Htransition.
  rewrite regime_path_has_phase_transitionb_eq_negb_regime_path_phase_stableb.
  rewrite
    (endpoint_phase_transition_implies_regime_path_phase_stableb_false
       descriptor state xs r rs Htransition).
  reflexivity.
Qed.

Theorem endpoint_phase_transition_implies_regime_path_has_class_transitionb_true :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    regime_path_has_class_transitionb xs (r :: rs) = true.
Proof.
  intros descriptor state xs r rs Htransition.
  rewrite regime_path_has_class_transitionb_eq_negb_regime_path_class_stableb.
  rewrite
    (endpoint_phase_transition_implies_regime_path_class_stableb_false
       descriptor state xs r rs Htransition).
  reflexivity.
Qed.

Theorem endpoint_phase_transition_implies_atlas_class_stable_false :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    atlas_class_stable
      (regime_phase_atlas_from_iq descriptor state (r :: rs) xs) = false.
Proof.
  intros descriptor state xs r rs Htransition.
  exact
    (endpoint_phase_transition_implies_regime_path_class_stableb_false
       descriptor state xs r rs Htransition).
Qed.

Theorem endpoint_phase_transition_implies_atlas_phase_stable_false :
  forall descriptor state xs r rs,
    packet_schema_descriptor_phase_signature_from_iq_regime
      descriptor state r xs <>
      packet_schema_descriptor_phase_signature_from_iq_regime
        descriptor state (last_observation_regime_or r rs) xs ->
    atlas_phase_stable
      (regime_phase_atlas_from_iq descriptor state (r :: rs) xs) = false.
Proof.
  intros descriptor state xs r rs Htransition.
  exact
    (endpoint_phase_transition_implies_regime_path_phase_stableb_false
       descriptor state xs r rs Htransition).
Qed.

Theorem same_emitter_class_iq_refl :
  forall window_pairs threshold xs,
    same_emitter_class_iq window_pairs threshold xs xs.
Proof.
  intros window_pairs threshold xs.
  unfold same_emitter_class_iq.
  reflexivity.
Qed.

Theorem same_emitter_class_iq_sym :
  forall window_pairs threshold xs ys,
    same_emitter_class_iq window_pairs threshold xs ys ->
    same_emitter_class_iq window_pairs threshold ys xs.
Proof.
  intros window_pairs threshold xs ys Hsame.
  unfold same_emitter_class_iq in *.
  symmetry.
  exact Hsame.
Qed.

Theorem same_emitter_class_iq_trans :
  forall window_pairs threshold xs ys zs,
    same_emitter_class_iq window_pairs threshold xs ys ->
    same_emitter_class_iq window_pairs threshold ys zs ->
    same_emitter_class_iq window_pairs threshold xs zs.
Proof.
  intros window_pairs threshold xs ys zs Hxy Hyz.
  unfold same_emitter_class_iq in *.
  congruence.
Qed.

Theorem iq_window_energy_equivalent_implies_same_emitter_class_iq :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    same_emitter_class_iq window_pairs threshold xs ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold same_emitter_class_iq, emitter_class_from_iq,
    canonical_pulse_classes_from_iq.
  rewrite (iq_window_energy_equivalent_implies_pulse_runs_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_descriptor_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    family_descriptor_from_iq window_pairs threshold xs =
      family_descriptor_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold family_descriptor_from_iq, canonical_pulse_classes_from_iq.
  rewrite (iq_window_energy_equivalent_implies_pulse_runs_invariant
             window_pairs threshold xs ys Heq).
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_semantic_tower_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    semantic_tower_from_iq window_pairs threshold xs =
      semantic_tower_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold semantic_tower_from_iq, canonical_pulse_classes_from_iq,
    canonical_frame_word_from_iq, canonical_packet24_from_iq,
    canonical_packet24_field_view_from_iq.
  rewrite (iq_window_energy_equivalent_implies_pulse_runs_invariant
             window_pairs threshold xs ys Heq).
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem single_pair_swap_same_emitter_class_iq :
  forall (threshold : nat) (i q : Byte),
    same_emitter_class_iq 1 threshold [i; q] [q; i].
Proof.
  intros threshold i q.
  apply iq_window_energy_equivalent_implies_same_emitter_class_iq.
  apply iq_window_energy_equivalent_single_pair_swap.
Qed.

Theorem single_pair_swap_descriptor_invariant :
  forall (threshold : nat) (i q : Byte),
    family_descriptor_from_iq 1 threshold [i; q] =
      family_descriptor_from_iq 1 threshold [q; i].
Proof.
  intros threshold i q.
  apply iq_window_energy_equivalent_implies_descriptor_invariant.
  apply iq_window_energy_equivalent_single_pair_swap.
Qed.

Theorem single_pair_swap_semantic_tower_invariant :
  forall (threshold : nat) (i q : Byte),
    semantic_tower_from_iq 1 threshold [i; q] =
      semantic_tower_from_iq 1 threshold [q; i].
Proof.
  intros threshold i q.
  apply iq_window_energy_equivalent_implies_semantic_tower_invariant.
  apply iq_window_energy_equivalent_single_pair_swap.
Qed.

Theorem emitter_class_from_iq_noninjective :
  forall (threshold : nat) (i q : Byte),
    i <> q ->
    exists xs ys,
      xs <> ys /\
      emitter_class_from_iq 1 threshold xs =
        emitter_class_from_iq 1 threshold ys.
Proof.
  intros threshold i q Hneq.
  exists [i; q].
  exists [q; i].
  split.
  - intro Heq.
    inversion Heq.
    contradiction.
  - unfold same_emitter_class_iq.
    apply single_pair_swap_same_emitter_class_iq.
Qed.

Theorem family_descriptor_from_iq_noninjective :
  forall (threshold : nat) (i q : Byte),
    i <> q ->
    exists xs ys,
      xs <> ys /\
      family_descriptor_from_iq 1 threshold xs =
        family_descriptor_from_iq 1 threshold ys.
Proof.
  intros threshold i q Hneq.
  exists [i; q].
  exists [q; i].
  split.
  - intro Heq.
    inversion Heq.
    contradiction.
  - apply single_pair_swap_descriptor_invariant.
Qed.

Theorem semantic_tower_from_iq_noninjective :
  forall (threshold : nat) (i q : Byte),
    i <> q ->
    exists xs ys,
      xs <> ys /\
      semantic_tower_from_iq 1 threshold xs =
        semantic_tower_from_iq 1 threshold ys.
Proof.
  intros threshold i q Hneq.
  exists [i; q].
  exists [q; i].
  split.
  - intro Heq.
    inversion Heq.
    contradiction.
  - apply single_pair_swap_semantic_tower_invariant.
Qed.

Inductive DeviceKind :=
| DeviceFlipper
| DeviceFpga
| DeviceRemote
| DeviceOther.

Record DeviceObservation := {
  observed_device_kind : DeviceKind;
  observed_window_pairs : nat;
  observed_threshold : nat;
  observed_iq : ByteStream
}.

Definition realized_emitter_class
    (obs : DeviceObservation)
    : EmitterClass :=
  emitter_class_from_iq
    (observed_window_pairs obs)
    (observed_threshold obs)
    (observed_iq obs).

Definition realizes_class
    (obs : DeviceObservation)
    (cls : EmitterClass)
    : Prop :=
  realized_emitter_class obs = cls.

Definition cross_device_realization
    (obs1 obs2 : DeviceObservation)
    : Prop :=
  realized_emitter_class obs1 = realized_emitter_class obs2.

Theorem cross_device_realization_refl :
  forall obs,
    cross_device_realization obs obs.
Proof.
  intro obs.
  unfold cross_device_realization.
  reflexivity.
Qed.

Theorem cross_device_realization_sym :
  forall obs1 obs2,
    cross_device_realization obs1 obs2 ->
    cross_device_realization obs2 obs1.
Proof.
  intros obs1 obs2 Hsame.
  unfold cross_device_realization in *.
  symmetry.
  exact Hsame.
Qed.

Theorem cross_device_realization_trans :
  forall obs1 obs2 obs3,
    cross_device_realization obs1 obs2 ->
    cross_device_realization obs2 obs3 ->
    cross_device_realization obs1 obs3.
Proof.
  intros obs1 obs2 obs3 H12 H23.
  unfold cross_device_realization in *.
  congruence.
Qed.

Theorem realizes_class_from_cross_device_realization :
  forall obs1 obs2 cls,
    realizes_class obs1 cls ->
    cross_device_realization obs1 obs2 ->
    realizes_class obs2 cls.
Proof.
  intros obs1 obs2 cls Hcls Hsame.
  unfold realizes_class, cross_device_realization in *.
  congruence.
Qed.

Theorem cross_device_realization_separated :
  forall obs1 obs2 cls1 cls2,
    realizes_class obs1 cls1 ->
    realizes_class obs2 cls2 ->
    cls1 <> cls2 ->
    ~ cross_device_realization obs1 obs2.
Proof.
  intros obs1 obs2 cls1 cls2 Hcls1 Hcls2 Hneq Hsame.
  unfold realizes_class, cross_device_realization in *.
  apply Hneq.
  congruence.
Qed.

Corollary flipper_fpga_remote_realization_transfer :
  forall window_pairs threshold xs ys zs cls,
    realizes_class
      {| observed_device_kind := DeviceFlipper;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := xs |}
      cls ->
    cross_device_realization
      {| observed_device_kind := DeviceFlipper;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := xs |}
      {| observed_device_kind := DeviceFpga;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := ys |} ->
    cross_device_realization
      {| observed_device_kind := DeviceFpga;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := ys |}
      {| observed_device_kind := DeviceRemote;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := zs |} ->
    realizes_class
      {| observed_device_kind := DeviceRemote;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := zs |}
      cls.
Proof.
  intros window_pairs threshold xs ys zs cls Hflipper Hflipper_fpga Hfpga_remote.
  eapply realizes_class_from_cross_device_realization.
  - eapply realizes_class_from_cross_device_realization.
    + exact Hflipper.
    + exact Hflipper_fpga.
  - exact Hfpga_remote.
Qed.


Theorem certify_canonical_pulse_parse_from_iq_self_consistent :
  forall window_pairs threshold xs,
    pulse_parse_certificate_self_consistent
      (certify_canonical_pulse_parse_from_iq window_pairs threshold xs) = true.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_parse_certificate_self_consistent.
  unfold certify_canonical_pulse_parse_from_iq.
  unfold canonical_pulse_base_from_iq, canonical_pulse_runs_from_iq.
  unfold canonical_pulse_classes_from_iq.
  unfold canonical_pulse_base_from_runs.
  unfold canonical_normalized_pulse_classes, normalized_pulse_classes.
  simpl.
  rewrite classify_runs_with_base_length.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite pulse_class_list_eqb_refl.
  reflexivity.
Qed.

Theorem certify_canonical_pulse_parse_from_iq_valid :
  forall window_pairs threshold xs,
    pulse_parse_certificate_valid
      window_pairs
      threshold
      xs
      (certify_canonical_pulse_parse_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_parse_certificate_valid.
  unfold certify_canonical_pulse_parse_from_iq.
  repeat split; try reflexivity.
  apply certify_canonical_pulse_parse_from_iq_self_consistent.
Qed.

Theorem certify_canonical_frame_parse_from_iq_valid :
  forall window_pairs threshold xs,
    frame_parse_certificate_valid
      window_pairs
      threshold
      xs
      (certify_canonical_frame_parse_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold frame_parse_certificate_valid.
  split.
  - apply certify_canonical_pulse_parse_from_iq_valid.
  - reflexivity.
Qed.

Example dense_window_positive_example :
  has_dense_window 5 3 [false; false; true; true; true; true; false] = true.
Proof.
  reflexivity.
Qed.

Example dense_window_negative_example :
  has_dense_window 5 4 [false; false; true; true; true; false; false] = false.
Proof.
  reflexivity.
Qed.

Example power_dense_window_positive_example :
  has_dense_power_window 5 10 3 [0; 0; 12; 14; 15; 15; 2] = true.
Proof.
  reflexivity.
Qed.

Example power_threshold_monotone_example :
  has_dense_power_window 5 10 3 [0; 0; 12; 14; 15; 15; 2] = true ->
  has_dense_power_window 5 8 3 [0; 0; 12; 14; 15; 15; 2] = true.
Proof.
  intro H.
  apply (has_dense_power_window_threshold_monotone 5 8 10 3
           [0; 0; 12; 14; 15; 15; 2]).
  - lia.
  - exact H.
Qed.

Example iq_energy_example :
  iq_energy_trace [255; 255; 128; 128] = [255 * 255 + 255 * 255; 2].
Proof.
  reflexivity.
Qed.

Example iq_window_energy_example :
  iq_window_energy_trace 2 [255; 255; 255; 255; 128; 128; 128; 128] =
    [2 * (255 * 255 + 255 * 255); 4].
Proof.
  reflexivity.
Qed.

Example iq_active_window_example :
  first_active_iq_window 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = Some 0 /\
  last_active_iq_window 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = Some 0.
Proof.
  split; reflexivity.
Qed.

Example iq_pulse_runs_example :
  pulse_runs_from_iq 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = [(true, 1); (false, 1)].
Proof.
  reflexivity.
Qed.

Example iq_pulse_classes_example :
  pulse_classes_from_iq 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] =
    [MarkShort; GapShort].
Proof.
  reflexivity.
Qed.

