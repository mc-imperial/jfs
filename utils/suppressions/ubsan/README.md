# UndefinedBehaviourSanitizer Suppressions

The file `ubsan_supt.txt` contains suppressions
for the UndefinedBehaviourSanitizer

Run the tests like so

```
UBSAN_OPTIONS=suppressions=/full/path/to/ubsan_sup.txt make unittests
```
