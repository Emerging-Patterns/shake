# Changelog

## [0.2.0](https://github.com/Emerging-Patterns/shake/compare/v0.1.1...v0.2.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* each command keeps its own bindings, as clap does (RFC REVIEW-16)
* a repeated option is refused; `many` declares one that repeats (RFC REVIEW-4, reversed)
* `get` answers Maybe<String> (RFC REVIEW-11)

### Features

* `get` answers Maybe&lt;String&gt; (RFC REVIEW-11) ([468c307](https://github.com/Emerging-Patterns/shake/commit/468c307aa2e150fae1ddaea717303fa7e3945b35))
* a repeated option is refused; `many` declares one that repeats (RFC REVIEW-4, reversed) ([7dbd341](https://github.com/Emerging-Patterns/shake/commit/7dbd3418ac7a79cfb8ea777a68ef688dd4ef994b))
* check reports a spec that contradicts itself (RFC REVIEW-7) ([dacf3f8](https://github.com/Emerging-Patterns/shake/commit/dacf3f856cb5552336807db4a9b934fcc7e0f144))
* each command keeps its own bindings, as clap does (RFC REVIEW-16) ([1b39897](https://github.com/Emerging-Patterns/shake/commit/1b398974ee9b087d20468404cafe2f0a4606bd35))
* short options cluster (RFC REVIEW-14) ([032b525](https://github.com/Emerging-Patterns/shake/commit/032b525d6c077df3a35dc988e75903dce3483ad1))


### Bug Fixes

* `-n=Ada` binds `Ada` (RFC REVIEW-5, reversed) ([100d479](https://github.com/Emerging-Patterns/shake/commit/100d4799f8a172da28735b1f01f6611f02582c21))
* a letter after a failed one in a short cluster keeps the failure ([3227fd5](https://github.com/Emerging-Patterns/shake/commit/3227fd5a6b3b85a77623b609da5902a6be6a1a20))
* a missing option value is NoValue, not Missing (RFC REVIEW-12) ([9517533](https://github.com/Emerging-Patterns/shake/commit/95175333f36219961e3c6a751b6e8da1f4fab328))
* a repeated option's last value wins for `get` (RFC REVIEW-4) ([c464a6b](https://github.com/Emerging-Patterns/shake/commit/c464a6b106029e3ecfff8e0ed6e2017f25fbe282))
* an option's value is checked against its own command's choices ([aa4f9ed](https://github.com/Emerging-Patterns/shake/commit/aa4f9edee2eda805d325afdf04351dec4ac56b94))
* errors name the command they happened in (RFC REVIEW-13) ([b5a4eb7](https://github.com/Emerging-Patterns/shake/commit/b5a4eb7e9bebbce5bfe8e394fe30f4259cc69307))
* parse refuses an unknown name after `help` (RFC REVIEW-6) ([6d92a42](https://github.com/Emerging-Patterns/shake/commit/6d92a4285f2b844b4b644589fe05414f3077407c))
