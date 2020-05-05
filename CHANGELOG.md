# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/) and this
project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Fixed

- The end of strings is now detected correctly in deserialization (#11)

### Changed

- Strings are now escaped during serialization (#10)

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

[unreleased]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.3...HEAD
[0.1.3]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/CosmWasm/serde-json-wasm/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/CosmWasm/serde-json-wasm/tree/v0.1.0
