#!/bin/bash
docker run -v $(pwd):/compiler $@ -i -t compiler
