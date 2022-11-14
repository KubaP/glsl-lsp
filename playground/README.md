# playground
This is a simple program for debugging the parser library standalone, without having to start up a VS Code extension development instance, load the extension, attach the debugger, etc. This watches some files and re-runs logic which allows for quick and interactive testing.

The contents of the `./test.parse` file are passed into the parser, with the results debug-printed to the screen, and the contents of the `./test.vert` or `./test.frag` files are passed into the gpu compiler, which prints the compilation status.

## License
This project is licensed under the **MIT** license - see [LICENSE](LICENSE) for details.
