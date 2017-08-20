# LeakSanitizer Suppressions

The file `lsan_sup.txt` contains suppresions for
the LeakSanitizer.

Run the tests like so

```
LSAN_OPTIONS=suppressions=/full/path/to/lsan_sup.txt make systemtests
```
