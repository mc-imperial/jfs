FROM ubuntu:16.04

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        binutils \
        cmake \
        curl \
        ca-certificates \
        gcc-multilib \
        gcc-5-multilib \
        git \
        g++-multilib \
        g++-5-multilib \
        libgmp-dev \
        libgomp1 \
        libomp5 \
        libomp-dev \
        make \
        ninja-build \
        python3 \
        python3-setuptools \
        sudo && \
    apt-get clean && \
    ln -s /usr/bin/python3 /usr/bin/python

# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user
