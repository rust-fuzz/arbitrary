## Unreleased

Released YYYY-MM-DD.

### Added

* TODO (or remove section if none)

### Changed

* TODO (or remove section if none)

### Deprecated

* TODO (or remove section if none)

### Removed

* TODO (or remove section if none)

### Fixed

* TODO (or remove section if none)

### Security

* TODO (or remove section if none)

--------------------------------------------------------------------------------

## 0.3.2

Released 2020-01-16.

### Changed

* Updated the custom derive's dependencies.

--------------------------------------------------------------------------------

## 0.3.2

Released 2020-01-15.

### Fixed

* Fixed an over-eager assertion condition in `Unstructured::int_in_range` that
  would incorrectly trigger when given valid ranges of length one.

--------------------------------------------------------------------------------

## 0.3.1

Released 2020-01-14.

### Fixed

* Fixed some links and version numbers in README.

--------------------------------------------------------------------------------

## 0.3.0

Released 2020-01-14.

### Added

* Added the `"derive"` cargo feature, to enable `#[derive(Arbitrary)]` for
  custom types. Enabling this feature re-exports functionality from the
  `derive_arbitrary` crate.
* The custom derive for `Arbitrary` implements the shrink method for you now.
* All implementations of `Arbitrary` for `std` types implement shrinking now.
* Added the `Arbitrary::arbitrary_take_rest` method allows an `Arbitrary`
  implementation to consume all of the rest of the remaining raw input. It has a
  default implementation that forwards to `Arbitrary::arbitrary` and the custom
  derive creates a smart implementation for your custom types.
* Added the `Arbitrary::size_hint` method for hinting how many raw bytes an
  implementation needs to construct itself. This has a default implementation,
  but the custom derive creates a smart implementation for your custom types.
* Added the `Unstructured::choose` method to choose one thing among a set of
  choices.
* Added the `Unstructured::arbitrary_len` method to get an arbitrary length for
  a collection of some arbitrary type.
* Added the `Unstructured::arbitrary_iter` method to create an iterator of
  arbitrary instance of some type.

### Changed

* The `Arbitrary` trait was simplified a bit.
* `Unstructured` is a concrete type now, not a trait.
* Switched to Rust 2018 edition.

### Removed

* `RingBuffer` and `FiniteBuffer` are removed. Use `Unstructured` instead.

### Fixed

* Better `Arbitrary` implementation for `char`.
* Better `Arbitrary` implementation for `String`.

--------------------------------------------------------------------------------

## 0.2.0

--------------------------------------------------------------------------------

## 0.1.0
