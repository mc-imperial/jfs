import copy
import os

import lit.formats
import lit.formats.base
import lit.Test

class JFSFuzzTestFormat(lit.formats.ShTest):
  """
  A specialized test format that runs each test multiple times: once for each fuzzing library
  """
  def getTestsInDirectory(self, testSuite, path_in_suite, litConfig, localConfig):
    source_path = testSuite.getSourcePath(path_in_suite)
    for filename in os.listdir(source_path):
      # Ignore dot files and excluded tests.
      if (filename.startswith('.') or filename in localConfig.excludes):
        continue

      filepath = os.path.join(source_path, filename)
      if os.path.isdir(filepath):
        continue

      base,ext = os.path.splitext(filename)
      if not ext in localConfig.suffixes:
        continue

      # Run test with LibFuzzer
      config = copy.deepcopy(localConfig)
      config.available_features.add('LibFuzzer')
      yield JFSFuzzTest(testSuite, path_in_suite + (filename,), config, 'LibFuzzer')
      # Run test with LibPureRandomFuzzer
      config = copy.deepcopy(localConfig)
      for n, sub in enumerate(config.substitutions):
        if sub[0] == '%jfs':
          config.substitutions[n] = (sub[0], sub[1] + ' -libfuzzer-pure-random')
      config.available_features.add('LibPureRandomFuzzer')
      yield JFSFuzzTest(testSuite, path_in_suite + (filename,), config, 'LibPureRandomFuzzer')

class JFSFuzzTest(lit.Test.Test):
  """
  Extends the basic lit Test class to add a descriptive label to distinguish different variants of
  the same test file.
  """
  def __init__(self, suite, path_in_suite, config, label = None):
    lit.Test.Test.__init__(self, suite, path_in_suite, config)
    self.label = label

  def getFullName(self):
    name = lit.Test.Test.getFullName(self)
    if self.label:
      name += ' :: ' + self.label
    return name

  def getExecPath(self):
    path = lit.Test.Test.getExecPath(self)
    if self.label:
      # Insert the label as an extra directory to isolate test variants
      dirname, testname = os.path.split(path)
      path = os.path.join(dirname, self.label, testname)
    return path
