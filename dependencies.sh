#!/bin/bash
if [ ! -d dmd2 ]; then
    VERSION="2.060"
    if [[ "$OSTYPE" == "linux-gnu" ]]; then
        FILE="dmd.$VERSION.zip"
    else
        >&2 echo "This script does not support your platform at this time."
        >&2 echo "Try to obtain the dmd d compiler manually from:"
        >&2 echo "https://dlang.org"
        >&2 echo "Pull requests for improved build script welcome."
        exit 1;
    fi

    ZIPLINK="http://downloads.dlang.org/releases/2.x/$VERSION/$FILE"
    wget $ZIPLINK
    unzip $FILE
fi
