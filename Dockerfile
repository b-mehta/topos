FROM ubuntu
RUN apt-get update
RUN apt-get -y install python3-pip curl git vim
WORKDIR ~
RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | bash -s -- -y
RUN pip3 install mathlibtools
# sometimes it doesn't source ~/.profile so just put in the path manually. 
ENV PATH $PATH:/root/.elan/bin
RUN elan toolchain install leanprover-community/lean:3.6.1
