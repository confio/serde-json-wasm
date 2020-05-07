# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/) and this
project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [0.2.1] - 2020-05-07

### Changed

- Remove unused Travis CI config
- Polish Cargo.toml

## [0.2.0] - 2020-05-07

### Fixed

- The end of strings is now detected correctly in deserialization (#11)

### Changed

- Strings are now escaped during serialization (#10)
- `from_str`/`from_slice` now work for `T: DeserializeOwned` instead of
  `T: Deserialize<'de>`, making it impossible to deserialize into non-owned
  reference fields. This is necessary since string unescaping requires creating
  a mutated copy of the source data and only JSON strings without escape
  sequences can be deserialized copy-free. The same limitation applies to
  serde_json, where the problem shows up at
  [runtime instead of compile time](https://github.com/serde-rs/json/issues/530).
- Strings are now unescaped during deserialization (#13)

## [0.1.3] - 2020-03-12

- Expose deserializer and serializer

## [0.1.2] - 2019-12-20

- Add newtype string support

## [0.1.1] - 2019-10-27

- Fix embeded enums

## [0.1.0] - 2019-10-27

Initial release after forking from
[serde-json-core](https://github.com/japaric/serde-json-core) at
[bf5533a0](https://github.com/japaric/serde-json-core/commit/bf5533a042a0).

[unreleased]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.2.1...HEAD
[0.2.1]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.3...v0.2.0
[0.1.3]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/CosmWasm/serde-json-wasm/tree/v0.1.0
