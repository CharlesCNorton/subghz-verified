# subghz-verified

Formalizing sub-GHz OOK pulse classification.

This repository is a dual formalization / exploration engine for sub-GHz radio
experiments predicted by Rocq and common sense, then tested on the bench.

`SubGhzOOKSemantics.v` is the monolithic formalization. The tracked data files
are the public bench record that the proofs are compared against.

## Scope

- Raw IQ to canonical thresholded OOK traces
- Burst detection and onset/offset soundness
- Run extraction and normalized pulse classification
- Timing-family invariance and family separation theorems
- Parse certificates
- Decoded frame-bit and frame-word semantics

## Data

`captures/` contains the direct SDR capture families:

- one quiet control
- `A1B2C3` at `te=200`, `400`, `600`, `800`
- `55AA33` at `te=200`, `400`, `600`, `800`
- `C0FFEE` at `te=250`, `500`, `750`, `1250`
- `DEAD12` at `te=250`, `430`, `910`, `1330`

Each file is a raw RX IQ capture at `433.92 MHz`, `250 kS/s`, `28.0 dB` gain.
`captures/manifest.csv` records hashes, transmitter parameters, and the
canonical full-file analysis regime used for the published family checks.

`families/manifest.csv` is the project-native family catalog. It records the
canonical class digest and the decoded first-frame bits for each tracked family.

## Current Results

The current canonical full-file SDR regime uses:

- `window_pairs = 20`
- `analysis_threshold = 131072`

Under that regime:

- the `A1B2C3` family shares digest `19f722404f38089b6308894a201adbf2`
- the `55AA33` family shares digest `b23944cd40c832edea40ca156b5455fe`
- the `C0FFEE` family shares digest `f0409e8cb4d2bdaba1fdd093301be576`
- the `DEAD12` family shares digest `a57783a97009fc13b6e255e487f6e7aa`
- all tracked families preserve ordered inferred bases across their `te` sweeps
- the frame decoder recovers `a1b2c3`, `55aa33`, `c0ffee`, and `dead12`
- the tracked families remain distinct
