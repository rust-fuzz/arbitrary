**Note**: When the [UnstructuredBuilder] is finished, the `front`
is reversed to correspond with how the structure would actually look.
If this iterator is meant to mimic arbitrary behavior, either reverse it
before passing it in, or use the more generic [Self::extend_from_dearbitrary_iter_rev].
