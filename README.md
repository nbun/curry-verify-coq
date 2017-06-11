# curry-verify - A Tool to Support the Verification of Curry Programs (Coq prototype)

This package contains the tool `curry-verify` that supports
the verification of Curry programs
with the help of other theorem provers or proof assistants.


## Installing the tool

The tool can be directly installed by running the command

    > cpm install

in the root directory of this project.
## Using the tool

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the module containing properties to be verified, e.g.,

    > curry verify -t coq

and hope for the best.
