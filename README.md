Hyper-Hybrid-Reach (Automated Tool for Verification of safety hyper-properties in hybrid autoamton)
===================================================================================================
**Author:**
    Ovini V.W. Gunasekera

## Installation Requirements

* **Operating System**: Compatible with Windows, Mac OS, and Linux.
* **Python3**: 3.8 or later
* **Z3 SMT-solver API**: Run `pip3 install z3-solver` in command-line terminal

## Running Hyper-Hybrid-Reach

1. **Defining Hybrid Automaton**: Create an instance of the `Specification` class from `hybrid_specification.py` with the parameters for the hybrid automaton
2. **Provide initial state and transitions**: Define the initial state and transitions for the hybrid automaton
3. **Perform verification**: Provide the unsafe hyper-property to perform backward reachability

## Example execution
Refer to the `\examples` folder as reference for how to run the tool. Below is an example of how to execute a test script:
<br>
Command-line command: `python3\examples\hvac_example_unsafe.py`
<br>
Output:
<pre>
Result: System Unsafe
Counterexample model of unsafety
</pre>
