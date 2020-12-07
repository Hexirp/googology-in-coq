# Copyright 2020 Hexirp Prixeh
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Base.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Function.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Base.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Function.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/OneDim.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Transposition.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Functoriality.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Application_1_0.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path/Application_1_1.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Path.v
./coqc.sh -nois -verbose -R theories/ GiC \
  theories/Main.v
