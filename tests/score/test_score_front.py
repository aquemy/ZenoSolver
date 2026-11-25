"""Tests of bench/tools/score_front.py, the scorer of a planner's runs against an exact front.

    python3 -m unittest discover -s tests/score

The fixtures are the homepage example (n = 3, t = 3, p = 2, site/problem/example.dat):
example.pddl is `zeno pddl -n 3 -t 3 -p 2 -d site/problem/example.dat`, plan-20-14.ipc the plan
of cost 20 and makespan 14 that `zeno --plans` prints, written as a PDDL 2.1 planner would, with
epsilon separations, and incomplete.ipc a plan that delivers nobody. With ZENO set to a zeno
binary (CTest sets it), zeno's own front is also scored end to end.
"""

import contextlib
import importlib.util
import io
import json
import math
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
_spec = importlib.util.spec_from_file_location("score_front", ROOT / "bench" / "tools" / "score_front.py")
assert _spec is not None and _spec.loader is not None
sf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sf)

EXAMPLE = str(HERE / "example.pddl")
PLAN = str(HERE / "plan-20-14.ipc")
INCOMPLETE = str(HERE / "incomplete.ipc")
FRONT = [(4, 20), (14, 16), (20, 14), (24, 12), (30, 10), (36, 8)]

# Normalized by the ideal (4, 8) and the nadir (36, 20), with r = 1 + 1/(6 - 1) = 1.2, the front
# dominates 0.84625 and its two ends (4, 20) and (36, 8) dominate 0.2 + 0.24 = 0.44.
HV_FRONT = 0.84625
HV_ENDS = 0.44


def run_main(*argv):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        status = sf.main(list(argv))
    return status, out.getvalue(), err.getvalue()


def write(directory, name, text):
    path = os.path.join(directory, name)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return path


class ReadFront(unittest.TestCase):
    def test_front_from_the_comments_of_a_problem(self):
        self.assertEqual(sf.Problem(EXAMPLE).front, FRONT)

    def test_landing_costs_from_a_problem(self):
        problem = sf.Problem(EXAMPLE)
        self.assertEqual([problem.threat[f"city{i}"] for i in range(5)], [0, 9, 6, 1, 0])

    def test_front_from_cost_makespan_lines(self):
        with tempfile.TemporaryDirectory() as d:
            path = write(d, "f.front", "# cost makespan\n36 8\n4 20\n\n")
            self.assertEqual(sf.Problem(path).front, [(4, 20), (36, 8)])

    def test_problem_without_front_is_an_error(self):
        with open(EXAMPLE, encoding="utf-8") as f:
            text = f.read().split("; Pareto points")[0]
        with tempfile.TemporaryDirectory() as d:
            path = write(d, "p.pddl", text)
            with self.assertRaises(sf.InputError):
                sf.Problem(path)


class Score(unittest.TestCase):
    def test_the_front_scores_one(self):
        s = sf.score(FRONT, FRONT)
        self.assertEqual((s["found"], s["front"], s["impossible"]), (6, 6, []))
        self.assertAlmostEqual(s["hv"], 1.0)
        self.assertAlmostEqual(s["eps"], 0.0)
        self.assertAlmostEqual(s["ref"], 1.2)

    def test_the_two_ends(self):
        s = sf.score(FRONT, [(4, 20), (36, 8)])
        self.assertEqual(s["found"], 2)
        self.assertAlmostEqual(s["hv"], HV_ENDS / HV_FRONT)
        # (20, 14) is (0.5, 0.5) normalized; either end is 0.5 away from it.
        self.assertAlmostEqual(s["eps"], 0.5)

    def test_dominated_points_add_nothing(self):
        alone = sf.score(FRONT, [(20, 14)])
        padded = sf.score(FRONT, [(20, 14), (25, 14), (20, 15), (20, 14)])
        self.assertEqual((padded["points"], padded["found"]), (4, 1))
        self.assertAlmostEqual(padded["hv"], alone["hv"])
        self.assertAlmostEqual(padded["eps"], alone["eps"])

    def test_impossible_points_are_reported_and_left_out(self):
        s = sf.score(FRONT, [(3, 20), (36, 8)])
        self.assertEqual(s["impossible"], [[3, 20]])
        self.assertAlmostEqual(s["hv"], sf.score(FRONT, [(36, 8)])["hv"])

    def test_points_beyond_the_reference_add_nothing(self):
        # (52, 8) is at normalized cost 1.5, beyond r = 1.2.
        self.assertAlmostEqual(sf.score(FRONT, [(52, 8)])["hv"], 0.0)

    def test_reference_point_can_be_set(self):
        s = sf.score(FRONT, [(4, 20), (36, 8)], ref_coord=2.0)
        self.assertAlmostEqual(s["ref"], 2.0)
        self.assertNotAlmostEqual(s["hv"], HV_ENDS / HV_FRONT)

    def test_empty_run(self):
        s = sf.score(FRONT, [])
        self.assertEqual(s["hv"], 0.0)
        self.assertEqual(s["eps"], math.inf)

    def test_front_of_one_point(self):
        s = sf.score([(5, 7)], [(5, 7)])
        self.assertEqual(s["found"], 1)
        self.assertAlmostEqual(s["hv"], 1.0)


class Plans(unittest.TestCase):
    def test_ipc_plan_cost_and_makespan(self):
        problem = sf.Problem(EXAMPLE)
        self.assertEqual(sf.read_run(PLAN, problem), [(20, 14.008)])

    def test_epsilon_separations_need_the_floor(self):
        status, out, _ = run_main(EXAMPLE, PLAN, "--json")
        self.assertEqual((status, json.loads(out)["found"]), (0, 0))
        status, out, _ = run_main(EXAMPLE, PLAN, "--json", "--floor-makespan")
        self.assertEqual((status, json.loads(out)["found"]), (0, 1))

    def test_directory_pools_its_files(self):
        with tempfile.TemporaryDirectory() as d:
            with open(PLAN, encoding="utf-8") as f:
                write(d, "plan.1", f.read())
            write(d, "points.txt", "4 20\n36 8\n")
            status, out, _ = run_main(EXAMPLE, d, "--json", "--floor-makespan")
        row = json.loads(out)
        self.assertEqual((status, row["points"], row["found"]), (0, 3, 3))

    def test_incomplete_plan_is_impossible(self):
        status, out, err = run_main(EXAMPLE, INCOMPLETE, "--json", "--floor-makespan")
        self.assertEqual(status, 1)
        self.assertEqual(json.loads(out)["impossible"], [[2, 5]])
        self.assertIn("no plan achieves cost 2, makespan 5", err)

    def test_plan_needs_a_problem_file(self):
        with tempfile.TemporaryDirectory() as d:
            front = write(d, "f.front", "4 20\n36 8\n")
            status, _, err = run_main(front, PLAN)
        self.assertEqual(status, 2)
        self.assertIn("citythreat", err)

    def test_malformed_points_are_an_error(self):
        with tempfile.TemporaryDirectory() as d:
            run = write(d, "run.txt", "4 20 1\n")
            status, _, err = run_main(EXAMPLE, run)
        self.assertEqual(status, 2)
        self.assertIn("expected `cost makespan`", err)


@unittest.skipUnless(os.environ.get("ZENO"), "set ZENO to a zeno binary")
class EndToEnd(unittest.TestCase):
    def test_zeno_front_against_zeno_pddl(self):
        zeno = os.environ["ZENO"]
        args = ["-n", "3", "-t", "3", "-p", "2", "-d", str(ROOT / "site" / "problem" / "example.dat")]
        with tempfile.TemporaryDirectory() as d:
            problem = os.path.join(d, "example.pddl")
            subprocess.run([zeno, "pddl", *args, "-O", problem], check=True, capture_output=True)
            front = subprocess.run([zeno, *args], check=True, capture_output=True, text=True).stdout
            run = write(d, "zeno.txt", front)
            status, out, _ = run_main(problem, run, "--json")
        row = json.loads(out)
        self.assertEqual((status, row["found"], row["front"]), (0, 6, 6))
        self.assertAlmostEqual(row["hv"], 1.0)


if __name__ == "__main__":
    unittest.main()
