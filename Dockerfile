FROM ubuntu:15.10

RUN sed -i.bak -r 's/(archive|security).ubuntu.com/old-releases.ubuntu.com/g' /etc/apt/sources.list

RUN apt-get update\
    && apt-get install -y --no-install-recommends \
         git \
	 emacs \
	 vim \
	 build-essential \
	 gcc-multilib \
	 wget \
	 unzip

ENTRYPOINT cd compiler && /bin/bash