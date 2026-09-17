"""Regression tests for the verification runner's failure handling."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_verification as runner


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        (self.path / "verify_rank2_poisson_sparse.txt").write_bytes(b"PASS\n")

    def run_mock(self, code=0, stdout=b"PASS\n", stderr=b""):
        result = subprocess.CompletedProcess([], code, stdout, stderr)
        with patch.object(runner, "SCRIPTS", self.path), patch.object(
            runner.subprocess, "run", return_value=result
        ) as call, patch.dict(os.environ, {"PYTHONOPTIMIZE": "2"}):
            ok, report = runner.check("sparse")
            self.assertNotIn("PYTHONOPTIMIZE", call.call_args.kwargs["env"])
            self.assertEqual(call.call_args.kwargs["env"]["PYTHONHASHSEED"], "0")
            self.assertEqual(call.call_args.kwargs["timeout"], 1200)
        return ok, report

    def test_exact_match(self):
        self.assertTrue(self.run_mock()[0])

    def test_nonzero_exit_even_with_matching_output(self):
        self.assertFalse(self.run_mock(code=1)[0])

    def test_wrong_output_even_with_zero_exit(self):
        self.assertFalse(self.run_mock(stdout=b"*** FAIL identity\n")[0])

    def test_empty_output(self):
        self.assertFalse(self.run_mock(stdout=b"")[0])

    def test_stderr_is_failure(self):
        self.assertFalse(self.run_mock(stderr=b"warning\n")[0])

    def test_timeout(self):
        with patch.object(runner, "SCRIPTS", self.path), patch.object(
            runner.subprocess, "run", side_effect=subprocess.TimeoutExpired("test", 1200)
        ):
            self.assertFalse(runner.check("sparse")[0])


if __name__ == "__main__":
    unittest.main()
