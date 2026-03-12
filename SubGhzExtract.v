From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.

Require Extraction.

Require Import SubGhzCore SubGhzFamilies SubGhzObservation.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "burst_detector_extracted.ml"
  count_active
  take
  drop
  window_active_count
  dense_window
  first_dense_window
  has_dense_window
  first_true
  last_true
  repeat_window
  flatten_runs
  rle_trace
  runs_positive
  active_run_lengths
  inactive_run_lengths
  min_list_default
  classify_run_with_base
  classify_runs_with_base
  pulse_base_from_runs
  window_above_threshold
  threshold_trace
  take_power
  drop_power
  active_count_from_powers
  first_dense_power_window
  has_dense_power_window
  first_active_power_window
  last_active_power_window
  pulse_runs_from_powers
  pulse_base_from_powers
  pulse_classes_from_powers
  bytes_to_iq
  centered_twice_abs
  iq_pair_energy
  iq_byte_pair_energy
  iq_energy_trace
  sum_powers
  power_window_sums
  iq_window_energy_trace
  first_dense_iq_window
  has_dense_iq_window
  first_active_iq_window
  last_active_iq_window
  pulse_runs_from_iq
  pulse_base_from_iq
  pulse_classes_from_iq
  pulse_class_eqb
  pulse_class_list_eqb
  frame_tokens_from_classes
  first_frame_bits_from_tokens
  frame_bits_from_classes
  bits_to_nat
  field_bits
  field_value
  hi16_lo8_counter_schema
  prefix12_suffix12_counter_schema
  field_counter_view_from_bits
  hi16_lo8_counter_view_from_bits
  prefix12_suffix12_counter_view_from_bits
  field_counter_step
  packet24_from_bits
  packet24_byte_view_from_bits
  packet24_nibble_view_from_bits
  packet24_field_view_from_bits
  decoded_field_counter_fresh
  decoded_hi16_lo8_fresh
  decoded_prefix12_suffix12_fresh
  canonical_pulse_runs_from_iq
  canonical_pulse_base_from_iq
  canonical_pulse_classes_from_iq
  canonical_frame_bits_from_powers
  canonical_frame_bits_from_iq
  canonical_frame_word_from_powers
  canonical_frame_word_from_iq
  canonical_packet24_from_powers
  canonical_packet24_byte_view_from_powers
  canonical_packet24_nibble_view_from_powers
  canonical_packet24_field_view_from_powers
  canonical_field_counter_view_from_powers
  canonical_hi16_lo8_counter_view_from_powers
  canonical_prefix12_suffix12_counter_view_from_powers
  canonical_packet24_from_iq
  canonical_packet24_byte_view_from_iq
  canonical_packet24_nibble_view_from_iq
  canonical_packet24_field_view_from_iq
  canonical_field_counter_view_from_iq
  canonical_hi16_lo8_counter_view_from_iq
  canonical_prefix12_suffix12_counter_view_from_iq
  pulse_parse_certificate_self_consistent
  certify_canonical_pulse_parse_from_iq
  certify_canonical_frame_parse_from_iq.
