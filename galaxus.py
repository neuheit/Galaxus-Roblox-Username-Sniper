#!/usr/bin/env python3
"""
Galaxus User Sniper - Roblox username availability checker.
Built by .gg/neuheit

Your own mascots: drop GIF / PNG / JPG files into the "mascots" folder next to this
script (needs: pip install pillow, only to convert new files). Pick one in
Settings > Visuals > Mascot. Rikka Takanashi stays built in as the default.

Run with no arguments for the interactive menu:
    python galaxus.py

Or skip the menu:
    python galaxus.py name1 name2 name3
    python galaxus.py -f mywords.txt -o hits.txt
    python galaxus.py --builtin --theme Inferno
    python galaxus.py --list 4          (built-in lists: words, 3, 4, 5, 6)
    python galaxus.py --list 4 --shuffle

Requires: pip install requests
"""

import argparse
import atexit
import base64
import builtins
import copy
import hashlib
import itertools
import json
import math
import os
import random
import re
import shutil
import string
import struct
import subprocess
import sys
import tempfile
import threading
import time
import wave
import zlib
from array import array
from collections import deque
from itertools import accumulate
from operator import add

try:
    import requests
except ImportError:
    sys.exit("Missing dependency. Run:  pip install requests")

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

VERSION = "1.0"
VALIDATE_URL = "https://auth.roblox.com/v1/usernames/validate"
BATCH_URL = "https://users.roblox.com/v1/usernames/users"
BATCH_SIZE = 200
CONFIG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "galaxus_settings.json")

# ------------------------------------------------------------------ built-in words
_LISTS = {
    "3": (
        "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"
        "F3id4bPOHq7duhbymarC1oGF6m5hfeXNv8/Qg2FvCQ8x778bi1nC959vi23skBNn6WoLnLOu31z7b3sswKjangt85mPCzux8"
        "xzkG6JI9IuzLjm8xsSaXc1dm5zqag8c/tw4K7ClZj13fD9lMszyuDutfJ6owe1aAuXdnoKFTqXOGJM+OnGbn4xbW/PWhsz7s"
        "dZ6O8uB8PT672KvG+siBonMzNngO3MB5Ko11s+oKst1ay2M+u2Rta57FWDs+zo1MWhfN52YxbUUH+O5or659PevEnjsvcwgb"
        "+7fiG1/6hvD1iG+fV+sFRjgGz+5cAudV6/PAzUZ8lI3nLJwBODgXEp02dyMnMBYIFy7ttf3PxD7Bauyv8bzec2bgLfL5aE3h"
        "ii9h/bVxbrh+73Ngz9jrOjuzp4XngKMDvMHzW/Bdms++aLjSA18QB52fM5j3c3a8vbA9z+FZFewb/spg/e/KO+LrRjj4DM6t"
        "zkxw9mc1YrsHcO7Bn0ImnCsDzrdwtNH8qjFnz0pw1sxubBj9GI03O0NzhqdxHThDF7FL+kKe18EareBNRKZXfKEqOY8ZXDHW"
        "h83oPMfB2I+9z73xJXiZdfna1sv64y90zoHBBn28x4C8LtYmlp6ZYJ1rCa8wjmqtIvLg+R3Wek1zOJ0pFO1fNF+PPuoPHRdc"
        "aWJN4MHW7zpfxzNTnMUy2PuPb8p+7q4Pfur4ylu1Y/bROBv05DvgC/d75OwfvpU1/finDTI9cM1caccnMG0Mo7VF7pX1L2JX"
        "hW9ygG+dvvCBnXVeMlhnTSd41EdnqNtjgc1Hl5/HWX7m3pEt6ySODt3BvoiLzr/D/t7/eZToQeFcSXt1kH/wvXWWm2eNTM7f"
        "tucP3/i1NsE8DLLurDDW4ROjWuUJ+QQTTrBh1Q8rwWfrGvAFW/t4wNsId0tw19XacvP+nsnhvG37kjwHxn4++PPuWQb2AnqW"
        "Cut04qPd+gQz61q6vuiMeU3sbsb/Xj3nSF5WOzvU3hrPLFmx255PwPfE1FIerW+v74edgIcN+ur2zzh7xpqA2zmwznYE5+St"
        "ved/DPBEZMU4K9g9y3mMPZoPtEcXHOrkdubE5FvOQY323TrzdmOP0bnyC4M1Fuj/+Z8jau2Oc9PgURt+cvT8GGPF/K5XJp0Z"
        "OMNtL/gU76JuwAuO3hnt1sNt6Kf18XI/5fQMXWe9RxnOyno794/PN8YGu9CDMwnZPcCe6DyOzzgna2cd/om/Bb6P+mvOI3OO"
        "8+r8EPPh4LjnPmBfLvPAxjf128GXQxzGFtXOHDBeDg6d1nev5n+tES7CsVrXac08vtiDP8T91ttaQ22BM4js20In//KrXN34"
        "Uzy/5znYs2oP9f/cHvACO1jr32J/7te+enhicp3BMXtFwK3WOSpg5alfAjYtyEX/7+9FVj7nTuCf/2UbfT3MtZnDrMPzmQMx"
        "f+2csh2f3fNE2Hvwr28918I5/tjZzVyyMXRjlvY/waHA3BY7Wf3rl3ln59wWcHN8ufNvQ3gnr4/utb2xCPvOkFXzxfCjEh3c"
        "busq4bOHtYsDnNTzozwHCZ1xjhe+34tN2Y1/O6eQe9bmZrCt22SfVM8zNvzMXnN47YRv5PxaOPJqvcRq7yccmGs17PF1m2dy"
        "Bjkyqh23vrpwbpG5emuLsSHJGa/OXfrCai/ciD9eOOtO/73k+Q5kEJ2yBkQ7A4Ys5t7h3It9Mfo92tKWNXceK7JYwCvWyv4H"
        "uTL7zf4eyvYFJ2J/Vr7XoP8Ze3tW1nOOyAr3a+wzmNA7cBFO3cmnwZHCGfj/2afOe+YZangv1/+st8Z+bnCC1fxltD5yx47w"
        "LMaTeN+Tta+sEePzEduxe36SvWCe/9Ji71iPTTs88n7W3nimyD/eLdcZws16T3Cq1DtbFD++tD7CecHs7YYNN266HWHWp8BP"
        "bZDPxfo5eel/1hE4dT3ghmePWMMDR7LWtEevwMaO53ydt+zMALjr/p+9MSHDcnl88926YK71x0pwhnc+4Aq7/qu11OzT5nkO"
        "j2fUzeGzBsraP2NAC/uLb306P/gCT83x1PgRnmXB/feV75oH28E+MObm5yvv2m32wzu7/cEX04Z71oG9ItYSsIfOrrFfCRt4"
        "ezaXfoy1Sy02D55bIVuTfNHzIC70qb7AYM9+YW/AneYs0Q+waPHdnPVkj5b9Rvic4uthjy3P7iy4scSuYgdYv85zApzf17Pn"
        "tef42OPOPqKzJ+sy/mfJg5H2PTnrAF+s+s9OhEsb6+7N/yq7YHQyv9iEVtvV4qPxuQ97PnjWCXh4KU87vNv63d4ZN9r1lXuZ"
        "70N+8QVa+8ixe5vnLE36pKyLs02vHU4Kf1rNYTkngPeCO6adfROjnRFnvnkE85Gn9z//Bn7qGR+d8xfwM/7rhG/v3Bx0oOzt"
        "08d/4HnnZHwVbmIM3rmo4NHXeV5EG5rR+lT76NvwTdaJs7/OGLO/r+nh2eaSWP/dvjnr7JEHrlnaj2BfkbUwYEICU1u40cZ3"
        "0iU3s3aRPXdNXnkoPv6gT+dMI7iPtVnGU6zJsDbRc0VK62yPcOADpNV5d1x3QYecizrecDVkxnyYc0aQmxkbGJG/97D/Hdz9"
        "1y95Ngvc3Pkzo7Jm7AhfYfLsM89JEHOdScw6JHXJvm3kAf3s0IvB3AyYkj50x7m4zsZo4aib/UAfPhQ6YA+fc7jhVAnsP50P"
        "5dwX6xnNN9qvYR1mjy+LjZvA+a82x8L92evLNQNTo2dCWENr/4dn+pTOyPeZeQb3enNOr74IXBadT3DHw/iMdvNwro51JOgU"
        "WNj/7crOH/uYnSOED6CPiC6M2Kb735dvLbpncFlrYx8r/MTaGOOsnb257IE4Zo4HWV+wB+3ewQ9YP/zxznNlPK9DLo3MZPkT"
        "PkLzoeNDw/Owlhf22xynds2Z8dGcMbJkbEGf93JWIfusfXrNZfM+Yu3sWV7OBAI7snEZOOi/x2FGzpBxezLNTzsf3/dFfjew"
        "oDd/9FTYZevi2Rv4WcuePdmzIJE7ZHLtnWUvT3H/8avR986YNBx3ARdGzzVxdvpgLRprA4aV1pqW9vw5hwEus3tWjLFt7B02"
        "+ZbTOPPWulnjDPjAtXPlonOsPVcH2bEurHTmtTlLOAO2ZbydIeOsNeev3CE9noXl7B6eBV045TfOkj02fBxrBWvkynncnunp"
        "eX/a84q9YC3gsjf24XuNx6MXxjmV/QE7g41ted4dWX4neDL7UyEvO2vxdNYnwiOtf/njo+eCOgMK/mt+c+C64MQMF+ms4fSM"
        "UufORfMmzvazz8F6oBL8tjahxJ9BRz0HB97yYqOOecGXse7CHBuy4IwR5xvYz+4elZ6Xh/4M+h4rcm8vURe6QyyAi9lvM1qv"
        "6qw+bLq2wXM5V2eNwiPwQxv1356WtuR99MXRPTBgPjwfDJ35rKNAby7ua52IfMcaycrZyzP8hmuzF9Gz/JzJgOy/l+dZgNf2"
        "BGMHCnuHnZnkmRtgw/UYv1L2PEvQWbRwOs93S85OZi88q4F7V3PNv8HV3jNS4D7w0ds5WObh7XHrte3O2zvRD2t5nFlfh9UZ"
        "Q71zdj1/ybMMHnwK8w74UNYHWCdrfEe/8x//tJ5wRL4rfm6/rLF5ZDV5Hl8PxmGr5O/mQT/8odecQOba8Kl/H8PCHuOreb6Z"
        "566CU7vzJltr2zv0fccet8ipZ3eUYXRuxuy5gPZtwrPLGxssp+Hd4Ah1r/+LjytvKdHP7DxU5zbz7Fz365330yGznj9mPGCD"
        "2xvfUQ65nzWh9oJZ5xad0WP+GB1y3bjWfpibBF+cveOswHPhO2DqDLdjry/PrDAODR7uzkMZzZ06j9laHfmS9gKOYf+o5zTC"
        "9TZ8jva2Tt/ZH6y5tcDmNOVp9su0MxzdmvshDKNxVWdfwmv1fZynbi2X9Uees1Z5FhT8pvH8GGTS+KznBsMPCuR8fI3D6Q86"
        "39K5pM4EtWfWc18vsNfzcMQFbCAYsaPri7X8novmnE57C5J5ugd/3vNgPJcV3z5bG8/eGKdwHv9/Fq78twbz1nANni2IH1w6"
        "cxKb4hxXrn9d9omyP9ncij1RYIW5s8UzPawPz+wT+1Y4E6rnGtb3IUuHZ/p5PqmxsC30rM98IdO1XMaeNuSI9yiR2cgz78ae"
        "uXfpeQDOdPRd7JtUJ6wxM+bUm1fD3/GcBXPYzp5fnK3l/GX2xbx79pwjbJh9SRX8xPrwaguP/QDOdbSmyhjN/+whZzaxDz2/"
        "N/YDjpyeTWhfAb74+j9zATw/nQtgvp33Ps0t9ciM/cF7qMHdfpfLOdvN/Tx4Rs/c9Ew05Ii9jdacW980g/nOUABDe7hn/88L"
        "ezYHuj/ZuyjPYm08U9NYY+U5aOKweRl0Gt5YGSvxzF1k7DImz56tnT0P1leaM/QsLnvSsfPWl9oHUHnOovVo1u14bgjr09oL"
        "BuZ7loW6NTuTskZ/nUcH93Lu5GbNDPe4nTGi3XK+MGtzyVt4d7Bv8WwU7O8Gl3gfsMozjOVNcOn2tQbd8y0ubC2yqp/ruYpg"
        "34hdPVnznvWoWutXPEMPW95oN5xZqa3lPTwTqhH7PKvxgLezF5PxROfdOifpBs94t0LehJ86yCeds4RfdRsfd+aOZ2HApcDK"
        "eM+hRL4e54Zs6JgxLmMF+o/gVmtfD7apwV4c5ph4pjcabwIrjBvUnkPsGTTqlD5bESbPPDm57+TZz3CYGd8cWUqVc8xncMgz"
        "B9Br5xmcxj/skdUei0X40js+ofzH+WXWE1lT4xx6Z5o6W2+AK5YT97R/E58d3egH++mxx857uqxF4D4L6+U5l541wd9367mz"
        "MVzg6O2sqs5+JXwqYz7myT/skbks8PdyfsuHDfzsU/3wN+Xw8AbjCCsyOFpXbl3TjU3SZwF37U1v5C4juG4dHTbeOJjnC+Az"
        "dp414FmcvfnFCUwFF51Li97Nh+tlLyBr9+8tNwa94jfB9exnMRZsnl55Qq7zMCMzxlDgTp+z1MFE1jef+Ces1WG9nDHl2ziA"
        "8wfByHIOgzzSc4HNJWATN2M+nnXl2elws+ew39ZzpJzpBb+139wY2+VMKmw03Gxz/hzfvTyXFN5fLvZo4athuwdnnKEbzwYX"
        "dg4f+zs6X5y9+8xnN8YrwHe5suf5er6N8QTPl3KmM9dr0N/T8wI8N7Hz/BA5s30BYLCze5zh+I8/ecapsXzPN3GGqfMJ0YvK"
        "WsITPmPOxHNrPZcEWdbm/PkkfoHnh9zO+HI+t77lyb+xE/JUdPLD18jo6WzsPVkP6Xmm9s97/nGPL+057hkeY9zfNUce/rWK"
        "C2tjTRZ6drF3g7Pw7AGwrz2FeZM/GzPVXvBd5xIgs5dce0Hu4HjD7Nxx7IFzGMCRAqz4nK8hn3+cVeQ8CLimeVuxfoA/KsPy"
        "LeOdCY7deu4lOGoe+7F3jnV8PL/Nvmx5sLM9PEOFdc7OnLHeyHN2ed5HDmdtAzwWezF5rppnX8+eEXuEtSrh//wMntOytu/k"
        "2Qj2PZrLNC8L7spZ5WuPOWFzth96D3689usqt/YFt+AD/qpnncib7wF7sIfJ2nGes/CcRmduOLexnrGJ4CWyV1q/J6c77V0E"
        "Y9075baf0TN9UjDemoK6B2/EDtYGW5o9m8b6QOR7fuxRhmOgP+PrmQTIgTL379fkmZxNYe0/MjY5Z9pztw8+Z82xZ7M19gl4"
        "hgvP62wv+5M95wq5WYwPG39kL1vrbvC9B+vwZme5Ytf+c4TAAmdQmpfb9Y2tufjAec9oYa3ts6rRpVfMtqbL+b/gIzJT2vs3"
        "mA9BJ8QS/n84rw7bvDXG6szRI+eDcW2wq3eWxRU2czYH9tRZ46znqlzYE+3cVufx956XPmKDxVfsXauv4hoM2Aj74J1P94XH"
        "M5yc03lgZ3bP87WnEr05xATzLBN765wedNlzeq3hcJ6cdZOeBc0+NydybOzR83Txj6ckTjnvEk7Rm0f70EdjxfB5Z+qBt8na"
        "14StcCb1gnxiI9PmPJ4PfojdRB978GkUV+C7Pfb69hx4Z67Zs+C5gwffcxYP/Cc7o4d7r87MWT13zPNM4RPOF+vwT4zns94n"
        "e3Z1xszh6ZnrrQ9rxDvM2C/jLbVnnMj38HsWcNS+O+dO836dvNG+RWe+T8if+ambZ3FmPFy2XK1zQYfQ/di719g06/PEANcS"
        "fb75e4Bnrisy54zhm+fsrI/1rBr7w53tzTt5Vi4YnXr0wx4Qe2SNoU3ohTMd4fHf4jlq6MBpHBjZj2CQ8Ub0rHQWhDW58PTe"
        "mQv2tvO9Cj582Kth73Tr7IeCn1nn69n07IHna//nU+FH9851N9+A7TBPWuOX23/6mkcGr5zLdNvXwO/lTiPvdNtbBy7Y63Zz"
        "/8kzlyvsuDV6zjGF+3T2hzgvBfwdtSe8H7yuc/YFOteOzh+z38Taanwx1x+/8XKWwv0iN/abP+Gwhv6SN1bos/E6/PvXmQZi"
        "+4Zdxgf8z7+tw2wNpTOSV3S3d/6U9cHo4b9vw7oHeKnn8DVyqwi3w2/3bEz0oPif/WOcuMXOYLc9s/i1vo73RiYGsP307F5j"
        "OuzxxHquyNl9wtOtR9qwtV7bHimweEUHH+P41qP/a0FKdBq+4hxYbZ7nzjzWi1tbag9NCxbzjH8fFrnwvC9wurcvkWcdrcP6"
        "4DjOIvQcYHudszVUT/jAh9pz/5wPDE5tl3ZK7gN/8yw3/cfN+fDImvPwRmPqB/h+ovPOlPDc7hNMZG8+9RDf33kL4nntHBNn"
        "3CG3nfXlxlqt5cem/s+TtWcNjoWtKD3Hj3eIzr+0XuO1J4M1sa68sc7NGivsKHp5rG24POetsXfeGB08dYcD2nPlLNl/jtYz"
        "5Dwnxvpu9ujzTB24/wEPK3k/9nqwdnLrwojczM4YmMHpZH+nvYrKlnNOp7A4kwKeXpWeXwSmwIdGZ6hF59OBJfZmXvhSsxyT"
        "tQJfPmM42P3ycL6zdaqeQe15qp5dKy+xBhy+ZQ7phQN7VjN4W7InbW+9pdd3pqt93GBPBgs8g0af7LUG1jma2P7LeUvOiQOj"
        "kK3S2Q7Jed3IxeQ5BeCBdtlcRmWvvLjOvlufdnjuE5xpyWG5rDtBrvyuZ+LIV+0h194YB+qMvdtLz1p9zrXlj+vC9QawcGe/"
        "Nu003CN3G8/gjIAP+cH2IoPlXoLL5gOsxwTj9H03Zxbbg+W52Z5xjH31TGBrkSdjmsY6PONwhCfhg/Wer/OGp7L+EPnwTBz2"
        "JIHl07+X1PkS7APvehpH+PewgxvWCf/PbwE74ZaN+RvkqsN2nZ4T+4Gx6nHjbB9kG1w8zZUfzsjBHnsWmbWAYFSy3vQC+8Gk"
        "7lAPsZurvf3WyYNpPF/dFfjS5iXB9lq5dhaa8e8YdmcNz55xebAH2EWu2YlTLRzXeN5flpxpAR9Fvxpj369xYOcpmwOC57zO"
        "w0W2nOPZ38iz+IzOROSutw/S+ZPc2zWA7zdirmdGndZmmvfFbhpHqJx1b1zL2WPmMHh251I4XwSfaW7Nv7Mm9kkvzvB3xr8Y"
        "oTw478tZ78ii5z+Ye6vxXbHLpbmVf28uPtjnrBfxgOeEg1bOMfeMTHsA/Y75QH3rCW5n3mb2fHfnU2Aj4NIvmHHZp2F9ovND"
        "0dPDXIDnxVbyK/zrzljpi89hfc/F/fU9zeu7t1UYnO1tn84q31Kf4X3O2dGmRPOhzm7B3pkbMNdVOreYNbk9g3KGK5oHXsF1"
        "ZBe/5/rnFL/Q2iNg3wDrt5t3gVcVU49cG9+XXxzwJ2NAzmfRh3aePu+G3Mfb+eb6RiV/T/AG80H4ycZH/r3H1jL0YXGmnrX1"
        "9pmZCwXzF3UAvJ48nwo7tLzOLQMTnd0KNq3ce7Omz1nzk7NQuK4zPJ1D7Qx/Mcgeswd+29hXbs2Y83I8f64Ij+cYyPPwkR9j"
        "62BrAc7f5m9OaxOw+yN+gXP2enutPPOW+1mX08LhDm0aemgvhnOJPCfZfmn2pnIezebZRR2Y2IEJcM9ee4jfjN1ezKN71rkz"
        "6O3x+cfKWeduQQZ37JyzGp21Jvdow+zMTevw4DGT5ywb48JPGpT5fYEbwYms7cZuDXD/3vnJPEf2/GltD378YLzK86rh4yu4"
        "PRmbdm6a7+QZUdY6WePuuejYusFcHXj72uNvbQ4YeY3GKuAc9tXKNf69fOijZ73aF4BeH4vn2vA9Z5dXzmp2Pif2we94hmdh"
        "bHsMs3mnDvn13LJb2buRW54VOT+Qg9maevRxBfOayl4bZ2lZZzSHzZ5La6nh7Y/nu5RwTfmdfeH/WhZn5FuTa6/+gE7phyOH"
        "m322rHdtTwp76BnocKqnl8e3+Dfo3mtexXpluJBndWnj7VtTl82pOOef/UplFy7rNDyfUZ/Jnhbs1vE/AxbbcxmjtT8enxC9"
        "aBbsGDa31n8a7cO2v1x8QOb08ViDZzNHg07AdzPvPhsTcuadZ9aCkYc1Plz7hcs31qQsypf5CvbUs69Yn9NZyPa3zHDUwnNA"
        "4BPJ3l/2RRvnXDpkaTX2sGNT7Pm9nQ2BLtg//T/D6eEZfT9rKayVgYPo18mhsKGnZ+Q82D3sYwvnueE1i2uHDc7ZmevO8Jx4"
        "P2e2X9gEa7TAMOzR+fcVaq7nLHLrZJ1PbO0i8mzu0d54z/ia8YHs48THH8xjHvhw6Hx0vtWq3ZW/e0YI/rnzNa15/J91iZ6B"
        "Se9sfdcDBgx837leRSh5n9t83793cuU+9muDZzdrao3H1eFvISMD9xuRs/85p/pXvIPzC+xFcI7Zjb38x1mdm4ZPhw7WYNVx"
        "4vPxrtdtvhc5BvtjOYQa+9MPPKPzVErxFEyyZt35AmDEY44fu145w8pZRvpim/k27ZUxYHtdrWnT74XfjRvvbfwXGzDZ1wEH"
        "yqzN7QytjTXHPiKnn2fUYv87c/H45D1yvq/mubWf2C/PGrE23jPTDud8cB17xW5n9pVwuw+MdMaLsqP9c73YX9Ykvur+B16a"
        "+4A3eZ6OsgkH/bhn7TxtYznOnjHnb27SeaHRvhP1DB5sXATechufdJapdYXPjk3ewXKe+eAa14pOoG/OGNUeOJ/C+irPrO+t"
        "u/EMOfwF/MfLGU7iMjJx7PbFGf/HB7R3Fdl5nafgjAVroIw5OT9pN0fqzD64q7WSYE2DP7V5/uMnpnp2vXEF+4wzvqn5Bnzf"
        "0foF+Sn2shtYqwV/w7PzyrB63uUJP0Q+F2uZPNfCOIR5aetFjFN7Xq25AXMKznn1XAv79E975rUVcmBnQeELOvs+GcuuwuSZ"
        "iWDlA5+8PC/G+dfo3vt0ofSMUezbIGcyZv0ak3UmkTWi9tV77i3Xs/40WqNrzsmzHOAdKzaaz3yeR+r5kvize7aGDz/DmoQT"
        "e29/pOeeOxM8W1/hrNoZ/wE8lm/ezgm3b8n5RzW4B054LmTv2QTghP09xg6Nxw/yIOvUzU9bjwRXfeWmnntjDhu75PlGvXN/"
        "7XuRv3rGmHYfHNE2okcvHOz+8zPzUSP6jn8jz5/sgbRm23OOjSWYe9V3NM+CHfRMNud5fAdrgM1z1r9zcVzDw9lpnt3esq/I"
        "gvO9PE/WubnHFRbPDasG7PEH5sLRW2ftWQdlzBKbY/8eXKDd2a9Ke2JeQg6DT7Y5gxnd9kyw156ojudwzov67bl26pNz5Z1n"
        "70w9bLGz9zwrxJp41vrGdi/YxXqwP4v9sEZiRz/RwxF+VGBTRs9GSNph9tXnRkdqa6ist/YsHuNzrN3rDIC/P2nPur6NZ2Ti"
        "k1SevYwMa5OtJV+NGyKbcOOvMjfqbFL7rO27sc6J9fMcBGfOO1MKvY3PzXshg85pM1dV3twHruScqIt38nwq88GH500799I8"
        "krN7sCeewXA4Px/fCX/xtr96sP/bPJ21R54dPuIbm1dA3+2BXaw38Qxq3qtxzrl5HP17+JKyzP0Pz8YyLiqe4kfFxrneD34Y"
        "9sUZ1J4T6vlt5nvQ66rVD/EMZ/ubkCVjagO8ybkgnvVe2vfj/PQ3nOh26UwBbdvjrCHsZT2G7V9XDU+1xxLMrvTV3dPWs6J4"
        "L+x9mdGff0039s4ZdnCu1nOwOmfK2BsLb2INhksfkf27D3jZCh+XR/D8pX0T/OxyntQKjwKj5J/Yzxn7Extr9eUu4IHz9qyb"
        "tScV7rwYf+A6E/d+e89RNG7Cvt/OyGNdsSnNrM/ahXt2xhwyaY1d5fxVZ3bYY1ngO/D9ynM8zK/ar4FtHO3T4XkG+0mdyQ/P"
        "MlZsbfypP46P7rmo44D8ed4Rflhc4Cs59PZFTs5TAavMQ9WeSWldiPOTzLtgl+259KwG608P9NCc+AQHNw6xc39rUJ1HyP1u"
        "Y2bYybw476Rif8BDz44ZPYvAmcSsoTrjjCPzevbjlvby4ld+9vDDZ7Mxoyr0s3EG/Xp8JWtDC/NF2BrrN/9nX43gumdYYP9r"
        "cz/YbWumnSN02rtiLsDzF56wO+fasw2cu28NmueNowMnHHzgPQqfs/YsF2vcsDmeLzqeyLVnH9k70OEz4G977jDceLC+x/oH"
        "c/aFuR7wv/ZsLucG2EfJ+lhnK0ZgNwpksHQeqjNNTnvTkRn8n9MZzJ67uspDsW387rNHMCG7zhOOV5hm69vhPwX3c1bXbY2l"
        "84ux586UMf/quXXYuK7xbHXPJmcv8ecW53ih+715U+xM4zlHxgCdUc+zHq8+ujXE1hthT+wZOmO4Pbsbm95ruz44woE/aQwR"
        "DLytUdR32c3DyTs858J5M9ZCwCuwZbuzc/5zFe3zd6axNt0zEe0/uMASeIUz4jx7ZcaX3G/8IWMa+jjO1rZm03OPsbnsWWus"
        "Xn/xADfQmRfueFr/PoHDnrnJnn+sTwW3nbVJnfOb4E7/vt8z7Po85p7Bs+w5ydnzTvTBje2gD8l+Nu2/PUfcGxw60fF2MbZQ"
        "wXPsNXb+tXk28I977L3nU+hfghnW936ex4AuzZ7JoFzBl+U128i6wMPEsxX5RdfK2lyYtfjIm7Fy86iXcQTPFynYQ/gTe/ki"
        "S7u13/8zL7A7yb52sKvkO579av0U+nlG7i+W2P+Ijvw6uqMkgKAYhqJ75Q/DMBh27x57eG2S1zY5b/Mymahh4e+ZPsUr6hmX"
        "G8t6J/ye6Yw0Xjx9eN3LmUPIpahWeY5XUyOffdl8S/wLh+IF7P/ALLDaWg+cMXyonzzn23vdw1c7mzLD+evb3U7Pykvb/IPS"
        "TM8HO3uN3w=="
    ),
    "4": (
        "eNosnd2a46oORO/zlhhjm/gHBuy4nafftSr74sw3+0x3YoOQSqWS+IRaX0tYr9cejvfr+KT2CmfIry0cw+tuKb2GnD6vNR/n"
        "q4V8vsZy99detkf/OS+vvpTjteQzvJZ0pteZ2vzaU6+v3PPxalfqr/M62+t97fXV0thfNc35lXZ98nht5TWUc3t9Ql9e4er5"
        "Ffawvc7l6a8QE4/R2isu+od85PB6ir6otCG81tDP11l6eIVxKa+YQ3xdx7m8zvBX9L21vdJfza/e9UabfkV/3PlVw7m/tvTc"
        "r3Toe/c46nfDNuvpe3zFFMbXfvXy6lWvNYf50Hvoy+v2nK/+T48bS9j10uF+9dAqfyQtjp5qCnnV4pRVXzTrK9N4vb7XFvQK"
        "4/6aUtO7HaVqhf70UfkvvZYy6EnLvusFU3jlvadXP6/tdaRwvM6mP/pWxldd0vZ6Jy3EzkP2Sy89ZD1f3LQfcQmXvly/Fi59"
        "VBjz91U+Ob7usvXXELTYZ/53vdLYtEfXeer5Rq3LokX8ZH3eeOlTzqYV10Me+rVyvqZL3zZs6U/P99HPpW175aY9Gsqh97ia"
        "FmIZg540Lq89b3rwqAfSwyctcU2yoTzpWVLRklzDK2FIejf9yNOu15DO5/WEnf24ZC9hu9iU7ZWqtmwv4XyFT2lapnl/nbf+"
        "drYr6oGKNnljA0ot+vK/zArt2u6jaf305j3ppfUK39fBqw6XNj4efN4V42u2/RXt29hkFtdRr1e9Kj83zvq8PL/mImPV/m56"
        "wSvo9fW++q+PzCJqJZdJtlH2QUvXttfU9EDpk5N2Rlv7LkuXgWixQ1sfrUvXSbn0u0feZaeHTHQveoL1OrqsM9vqWNPx1v5O"
        "06tmmd7GWVjTGbWrbXyN4ZBNhmfXSn6DDO4Jsnb9f/kot35EBly133rIQSeKrxw2rdV0pUMf9dVR0zq97oSpFO25jPp6zZde"
        "sB+ynAOLnVO7XzImLUQe9A9Fh33MYdCp1fr1o2iZkk+8HryVU38knYB8pOeVJtn4mGUMOQYM7o1Z6POWLBuqW3lkFjokd9Zr"
        "taQn6DHp4Ow6aloRnY9Hhv6RwWiF1qwnbVomjv2OzxnY0LDpX3vRH62UTR+lv4086RD05WnL4ytFHbDp6nipNb10gmbZvaxz"
        "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"
        "n/4PddMnKQ=="
    ),
    "5": (
        "eNo8nddi40iyRN/5lwVDACLcwJBNff2Nc0p7X2Z71WoSKJMmMjLy3MvaPbZ9P7ZHc5/t+Dj79nU+rnGb58e8rV15LGVay2Od"
        "1uF4nN+lmR/Tet7Ho93W63wc/TrMj2Xq+vnR3e11P9q+689H6aZhfLT3Nb0fn4n/XttxTY/8aVof3dSe56M9pr57zP3Vr485"
        "nz/lc86lPJ7bkZ83pX1Nj2N7l/nxKld+kofqtseYzy+Ptqznxk/m/vFzd337aMftPvOcbb7lHKfmeDzvc8ynlbbNT6Y+33ju"
        "5eAZ+JbWT+76Y/s8+n9ZiDwJbzR+9+18DMf07h9NnjDPOZf1epTzOvpHV46lf9zX1Wc19r67s2785Mw/On3OmW98NY9mG47y"
        "2PzN0m3t6/HZjlf/WLc73/LujynPX+apPM4yl3z+iyfMu6/5tHXLZw7bO5+WV8k75v3n8mj6eTqzMkc38715lzYf8Xrkx3nC"
        "pcz55H5ds1ZHf2aVxuna1uzCmTXJvyot79VejyF72j/yBNnZpV+3vMu957vObZ6ux3Yf+XnWv/Dt59U/8tL5nDmLtz5+tiln"
        "413yzVmZ6WpzZs7sxXD0+du2LKzY0bdZvanke9u5/075BPb0bPs1Z+Pq8wxdjtXxePV9x99e05JTd2z3Y9/28ftg+dd8S/7Z"
        "45PXG/JG/TFnF7LnjzXr9ptna188Cad0mFjnZSrrkBNSuuXxnLdhyy7PW8MzHOvj6e+0LGi+xdXImewfOf3bK3vd5y2y5MeS"
        "t+AuPPvjLKzkOT+OMnfZl2tap8eexctbzEueP+vbLzmH/ZkdzOOU/HdkHfL5++M6crceZdnLmWdbs8JbO/Kc25l9zKpm3/Pt"
        "6zN3KgfiMcz9mTPft/nk87qPK2tSjle+a+6HvCMrlgXOXuc38mnXUZ7PrFUeK8+wnj0nOSuWt87pPXjEfHJeMiufQ8YdzHPm"
        "FM0553nC7EiW/51vbHJaply/lpPZ5BOOsmTdSu5H7mCTlclf8syr92jkduTO5GY1R2maB4928FRZ+XYbpj6/z9nutn/e9zy1"
        "J7/PLfvmE7p7zvrnE/ec7a31Jrbb8ljuIzfxs23Z0zELx7ccWaWsT+7+SyvEQuZ29Hm/x393Dv1jvznnsU75t6ze+ri+e2zC"
        "nGvX51Zm5R7DnXP36C8sSXNsWYfWfX/mtORex1z1rEn2Nzc9n5bbntUbsrFb/hZLklfM/XpOnPzGE5XzsLGb+R6ep4m1mTlF"
        "Q2zjlvty5fxnj7mDZX2VPM/wzb+ayyd/ntjlZx53zF2+ppYT6N3k354jJ6qd77r+DRaAs5oTm98cXaUmt3XNjrdZ5+uYGvbr"
        "aO6sG7c79+IqOav9uWfND/Yr1uzjCl9ZJc7AlbuT78ojXtzWFau45r7kFGWFP+WbFf7ErOa29vuY2+FzYrRWLM/xzdNeBcuz"
        "Xt98b0xk3qXN82dfcq83v2ve8jac+fxtzkxO+F4GbVTODtZ14RT5LdO9+KbPzZXJvmfhY5dySfbY+Vj3fG9OR1bvzPnPqc3q"
        "tdu9Hvz5aLkF/cW5whL+y5HKmuTQ5C5wBnKqc3cw5Nnl65q/+c3841iDmRN7Y21yu/Je99rE/pTmxO/EqFTL0PIWO/doiZ3M"
        "z/E1PR6n8y68J7xnyXL0fmZWuF+73JcsBnv01ULmb3I2vtzEGLU9azvnVMzb85n9PVi3ZzxOPvnF7y+5C98828m7b6ufMF9Y"
        "11z4rLzPPPPnueTK5ffX/h3bEvvq+Y8Nv/nzM+YGLzDkvWJCYivyOXmGgauVt2BtP/nkvMuBXys446xVLmGsRz40p+WIf8/q"
        "lUFfs3E387457SvPfMdONjlRM++4z6xnw13gduDTF/62zd3JhnAerqzhT2l7ogjsQFPmjf3Cn/Ir3qM8+afnzD/vmZPjd2GF"
        "Lj5zikXd8SBZ8hc2bbvwRPji0n7jg/LJ2d+8S/xv3iI729wrHvZu8m+PjdU454Qv+YT8jPfKTuWs51vu9cozz9n42Ks+ljjv"
        "iwf5jFNsNTYhVvrT529z4xJBYcFmnuRmVb3dhYhi8Z62X/7tPnHvcq+z/vH7+5jblPOS54xBz/khmoqtwP/enJ88DtZ4W/K+"
        "+fbEDPEp+ds+R22KxebW5F7vRCbrgF/Y2dk5tpzfP+7sGncttwlrv0/YybjnnRXGk/b5f488LCc5Z6zjROX8DFnCSetx8VR5"
        "i+HuLyKZjluT4zBowa6sEh4NtxCf2+eSxC5xunKIpv3R/3fnLX5uIoe30UX2kZWZuDsxQlntPFui0HeNgtqrJwpiR+Kzcs5z"
        "3PhXsQYH8VK8WGxTnmrsV2xLHGYiqPaOF0h8dcWWlmvMk+d9sV3HgdX95F602zfPNrj77+wCv7Pde+K92c/p+MzCWy881uPF"
        "9mvl8Mh+cu5mPiHbgs05ltzuack53z2fuXfPnKj+Gbv0nliHpSRO1Bq8iNYubFpZNlc1frB8YmNzhvPf2K7EJLlfWassYX5S"
        "jJxbz3PioY5/tQ43npc48F5PbPgVC3/OX2LXeJmczB4/m7XOSTgTdp+sXjxgvFI+52Os9Tq4C30sTMteJ+4674lbE0u+8i65"
        "IzFIJ2uC54rlPbHP2PytJdKIwfhic9gFXDH+dMK2xxIWbk1piPBfz/z5lfvVGD/nDK+sLV4MI7dybpMj/NxDIv/sVGKt7Eh2"
        "eZ045+1xd13WZM5qF4I8POPkqTiNLrBa5c4ndMaZiVPzOfGJWYd49tz6pbDjxLEHnjf36ySUzJMUrIeZTnlyK79ZGLzhMSfG"
        "MMKJTSa/uM98171ioxJ35px0Cbjwa8SHHJC8u7vfeDdLx/rnW/JdY8/ZyA3Etkzs8pmDy/nJVSdaXnkGosRkLlnz3IreWPo/"
        "bex0x4fGQWqHiQRYq0RuF5ZzXbM+9+wabkRNm+ct93EnmorNj59dyZ5ish85H9mds/6rA3s1+5Nsfv7VvXY3ljm+kR1pe2/i"
        "QXRd2DXj9vyAiGXn+bVmic0azl4hVvkmqPWuYan2Mza2x0rk9/X1eT+e/7cQybMOJ1aoqyfhbo2lOSHNdhB3jdwXbvr2yE5M"
        "xCR3zkZn5vg0lyEoxmKvLdZ4w+vl+Tf8KbFcLF58yr00vAvZSndo4Y2Tn3rte2Wn3tqZD4lEvj0+MBEmpzqxd+F57qHgTeLx"
        "ucW5ETeRTNd3xD+Fs5FdNNpf9hvLnBjsaaZAfIhnzzs9yp5gLt/IHmUdTrzemshkiEFNlLuR6XwKb5cgKKudZ+C7tjjd2Em+"
        "JUY08VV253cy5iTGi4PP+STiXY098iDY9sTDeHDiAXJD/VT2Ojl5rOJZYofYkZz8pufJk90nq0qik7+9XLenWV5OV1bg7Hts"
        "4HxnfXJu30bdsYd9/uc0EjjxI8nFsoFDbs32Wfecpfzj/BnfNG/crN2b9bsR+8VblIXcvxu43fnNrOnc5QmJDZLE5y4k9cnv"
        "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"
        "Yq2zHNfDHIRg9mt2wL53Zq+qI26HnP+Kc2I9PuI/dIyaCVo//fcd5FejtoTeWmO8OlattpV7ehi9gAv9wp9ZtLTfimC3ZlIt"
        "8SRdk95fshKwZRESuVJQGOT+qeNa7z5VnuTvMp2oX6x6h6c6RXeuUe2IJ2YgYl/lW9IEzA5+Z6PlSZRprhE12IUqT2IF8Mw5"
        "D+Qgr/Jbe0I39Fr1idlSehzwL511wEMtEbp+Rs/MbIQTC2Mne6O+RKMOcHvcfxUfawTyJ1WftmPlKetplsEyyjZs1anIt4Or"
        "fGcZ+66zqndoL0/85KD7D4T/oy7f3tNJOts9So/wAt9bZG8F666VKXkpiZTkYMBmPOQunnIvcz65udU2FioIi6tB1o9/By8F"
        "NmjlF23eXKvMKoPpN+Pfk4OQZtg7sIsviRCiF2SP0vF3Go0T7J1ZzKrIZ2XQlU9+XlWGuLlQzmEYwkdtt9pDURGtTo0g+1IL"
        "1aVdDgwsHdgp2wsdg8mOKpC90botpSfVbqvyA72x8yUuN9dbLw8E9dEEj7njiWcqb3OFPUXs3f3xuuHVzBtYDanqWxvVq6ex"
        "8rd7ZX2TO8ANILgzhtnEyqzckWkm0DASg9mSXBiM3Xro2cNgIUZCY5aK+YEgoMpd9gHRHTxSK0fhUAt/VZ0BMjhq36P9Gk9Z"
        "T2h9y1dZRFfgxIp3tWbos/pmi7eJLCz//bKS+Uy6ZlRFQMRxtX+WHhzsebOV7q3+WI1mvzLl+FvViqzFv0UXabsk9m7INQ7w"
        "DfhCdD006CGrQlbsJkD1cbJK26jJZjSb77rs8T/t+eL20Q3dq1HGDaKjARyAOBzk7bTLFXxJxTYITKxGJ66CWtc01yioBZOn"
        "uz+ervX2XdQOiGPPm9OCMsZoz4X55ol6ngpv5VMqB6kjFzjtZGzx78Z1c/8vP3nK/6ydzuO9LPanDOzdBKtNDygru5WV3f/j"
        "jT7e/QKpxSxefs4sGtYPPrN4SOLPzaxw3aiCkQqLRJ0qH9KFp+7BW6SFvuzdc3V6Kg6sFhZ+ek9WcmGMVJupt/rPTHMsvYjH"
        "WSvXearRWk9jXS9hJvyQqXI+4wlVU7mstrxRVJtqznvoNTZZ6JenjhoHaPBn5DSufuYyVV1Ta1I9mP9zwo69/pCf16T++QyX"
        "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"
        "AWtdNSvwOzmHlEx8dl/69Xeqk5J26lb0FHxX1X3VB0bagNof+yKv41JpdpWJd1fWyvS/OaSeipr1yFfkFs/2OK9qO3zshWn+"
        "N89uQO3TaaEq0n/l+DXqwHQyKlt5TYOKQ4ccPHqCLrMbZm6i13Ex+kvVwdF+wyKevzpPnH1cZGirbGnPF6G3OOT2Ad+wE3O1"
        "z4uqblMn7+gdGrkru/3p76nm+1ZbStWa28wuyUAXShT0FqnpCvO2f9fJ1+gC7eaATO9C7ZZpuZMzptu7dtOTL0PRJa4e61SI"
        "1jhZv4lG3KhXOkSbT+OrdaoRApnaT6n8vdprQy5fGjtBoD/iuX6s652VG6wS5j4aS/ROSyfvPuu00Le9UbmzNNKBX/35Vqy6"
        "3a/Urers+Invbc1NLmcQt9YXqPJsi4r3TD0rp2yWid6uQ93g1YkwAK7qRMXyr1/Vm9VFhCBAvyoVOqoDRIPsL6W/qpPM05bX"
        "bX/xRZ6IxZNhWGbZnn86M6XO7lEDQbWB7P5G3irqyHsxYkhuQ+ckJlQLnJa4NQ06BscUew7EqDp9ccZW5+xs2K13ndAKbt9u"
        "jbNdWI2rX6uy4mLHELYCU8WfhzqBDmUSJ4D39LAzUZHuMPi6h/qBS19r93UuNryvXQ4wYEyHBWvogJMv3ZKDnPs0d8bbq8xA"
        "cxnYkh3f+1Svab+JLpqNOtoh+/qpZxxVLm2duLFZ5czdL96yzmoFHSLalmWrXbdn1Q/s8WKX3Zd2wNnx8VQdCyRzwMfZ8ScO"
        "MLU+G9l9JzN2cY5boy9o7WCiP4tqDl0Jp1r6gwyoznyfymNle6ogrbLuZ7YeysxuNSWWIqZNw4991pcKG6231fzIKJqqyiEa"
        "0DpPtpU9wk454UK1JXPS2SlR8oj2qa0IyUHNgv7N/X/zFPpdrB6W40vG8vT7ax9K66SGREdiEU/5dSiCFhGDxeiilffFjFq6"
        "gIF767SU0clWVtluI+pD1HSo86rYHWfKaPfizVXqmNQUmuVydyppn3JprqrqCaZ3qqGRo9HaU/OFg3qpt7PWPSry8NVMHipK"
        "tss8rBwYZrpdFdMuZvpVQW6Qw6AiimtblXXrDO62oxtaluBu/TdrV+vaRJIFjYjkOKWqr892n6nHBea5HSKWqKrCo5AbrAqW"
        "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"
        "wAvuPyX0bY8="
    ),
    "6": (
        "eNpEndmi20iubN/1l0kyRWWJU3OQLH/9xVqgz33patt7S2QOGAKBwLxOtZyP7beXsz6+5VeH8THUbq/D41iXsx6PtoznujyG"
        "sgxTffT7NXfrY93Lp+6Pvpztb/zl+l3iJ7d1muI/87o82/kY9zIdKx9Wpha/t/7KEt8wnW15vMs8x5+O0pY3n1mHoT7GMtcz"
        "PuXVlqHEZxZ+stvb2T7xn3Wuy+O1+hB7PeI54heWpR2P4yx/1v2x7fX5rI+jHvHgjyPfqC5nPPDjeNX+VR6lm3hc/rLVxxY/"
        "EF90XPsRnxJPOcY3DPXT+vL41v2o0yM+o8WH9evS1y3edll+8SlDLEl9dNe+l+Hx3NfrqI9pHVmCiyWLNyrH5oct8bPxZPHY"
        "9bGsS/zi47le5/R7lON/V9kf8XOxaI9uLftwxLosZ6xLV3dW99umsvTxn+UdnzK0+LvzMZV4zOOxfmJ1z/jJoUwTD1jPVzzu"
        "xpq1eNr4vWebpvhTbF7dl/jaNd4lfuE8WcEWy3nGX+5DfNH6qdPA0sUDl8e5FxZrm1qs5eNVZt5vr/GFsWaxG8vwqG1ceLH4"
        "DH6ynCx59yp7LPkYj3byDYVvj3eYYnNidWMpH10swBqn5/mMP8ZnbnVv8Znjy8O3D+v30cdKxiO91nmL5YnDsE3lMcQixzu8"
        "Cofjcb5iXY946blNw+MssTpxTNfliPc7zvjI8dG/4nzFv6179fC1+LRHNxVO3b4eh6s0Tr/mKY8HPOI8xxIMLY7WGts4xIs+"
        "5hIr2h5r/677Hjv2rrHkrzXecmA3jxaHIV4h/nJceex4zT4emIV0b99t4iLE48XycDRidZcSjz9z5mMR4hd2duz4liMWOTa4"
        "xrvz6JzrLU5i3JX40j3uQ6zgEa8SW3zF0YibM+7s3xFn8L813oWV35d4sti864xz/b+rnf0jXmfyck280Xddh2t7lJMfjZ1u"
        "fZt4zfg/8Ub7+briPnQtzmfsUB+/UDmlnPl4ivJ4cbn2x8naxVpv186dbt6OpX45ivGZHY/L0WgPtiYeKf6vliFebD3iytS4"
        "SdzpLpYuFnNkCfpX7PHjF8d7x+gcHqI6s39xRuuxPcYaa35y2I9vffwXhogDVhZ2Ja7hyAZM1aXrWeUH+x2PFAdpiveLu8Jl"
        "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"
    ),
    "words": (
        "eNpUnel66zquRP/7LTXZ1o6mI0pxnKdvrCpQTn/3tuyTnXigSAyFQqFpp+HWdGMfl51nx63p4z8eQ1zGOf6335ppeselrLdm"
        "bof47+UxTLrG823jBbZ9jJ/s3TMuQxOXOf5i39fXrSnxs2ONVzqXeO3ziFd5NV/xNz9jubVN+45L9xWX/jHE9YvLNMVl6bnw"
        "LzuXwj+UsYvrcWuHJt4rrjuXoh9w4Q+HiWf7Hi887j2XI3510ptMTT9w/eW6xqdqpzOerg2/uPIS68QzXmJd+Jf1i8vMhZ+V"
        "+Mzrz63dm3Hh+h2/E984/mYfeYN91NfYx8czfn3Xn8cy8LtnrER7jrz+uSzx6c6dD86Pu6aNl4trrGXXTHNc5i0uS/+O68YP"
        "d112/rvwNN64e/IhuO5c95kr//gcmo3rwM+HeJPuOQ53rvHmXCeu8SvjEa83NfGlumloFl3jb6bxHr89rfGF4nr2XOMrdCsr"
        "3bFCcVnjF9d54AfxJeMSL7ruja4Dl4W3X7nr3c7ix/Wu53zhvfmNt46Vm7kO/OvwioveR0vVne1w65ul4xo7oOfv+ib+vWe9"
        "e75dXLa4zCs/LPE7w3fswz7ueFxKt9769RH/i4/a6636fYyP0O9r/NUZH6k/iy7HbWgesfbx7WOvxIZ634buud4GbuYw9fFW"
        "wzQe8XzeYsmGZZh13R88/Fu5HvzSf2csQOy9eMfhO3520wcafjhX97hPb67xFvdmHuKydPwgbtydlb038Q537sB9jDfluse3"
        "v487l/j296nxlT+ehlj7+8SmjWu8YVxfAw/xmmt3lrjqz+N28OKxa++x0lx4kX3lh/s5xvWMDXE/l9uDF348+ZfH2CxcY7ke"
        "8bq3xxpf7MGtf8TNHLjGronrOy7DEH97coYeJ+/1OMc4Zs/m9XV7sqRcv99x3debdt9znXjRZxyx+PG6x6Z9rifXc45tOMYb"
        "xCs0t3EOQ3Qbv9dYuH8c3X/DK0wPC/7v5N78O+Oc/DsXbt4XH+NrXB5xiYX8WnQGJyzKxHGasCixgrFGE8s9sdyx4e+3yb85"
        "xjaaYlu847rEXYg3D3MzN/9WnmPnZpm4me0Yl8LTwtPCzZ+bQ/8YtiWORSzXzMu+42GK3xnjzecx3nZe421mfdv5xJ7N73LE"
        "gz/usmIDlpV9uHacyXUa46zHSXs0t3WLr7jubdy0dWdXrgfvvIUdOOK69E1cN/0kPmJc4u03mcq47lNc+Vwb637b4g6vcZ3C"
        "rm3jTyzrNmFP4sqLaXXiGi+wTrEYmzZX2PnYInH95Ypp2M4pvsl/J4v/34kNjGvszL1p+Zh704/rTdYSY8n1N5ZzH8JMx7WP"
        "/4Vl2uMrxg9XrOCO2eHCi6zx2vv6jg+9n+EpZBgKe6LoK5dm4hJLW8Jsxk/D3sQPnk0fuyseYhG4bnHFUsQ1Nl95sqvjGotQ"
        "MIPlyVvGNXZqGSc+Svni65cvNmuJDVEm/f3Ezixs3TLjpErc2/jBvMYeK0ujK/+oFSth++KDbRyXohtStmHgJ/oU28gNjIc9"
        "lqlsevNY2Ni+5eCvjyFWqBxrWAeub6584vPBv8qDlJN7XV76Pq/YEbdDLuQYcc0Ht+oY4/eO8YiNdMh8H7qPhyxyXMM6Hbo7"
        "B7bhkBM7dixiXGMPHud+xCueU/zW7Vw6ni+4jXMP53z7bvCfcV/D3HzHF1rjymf6XlmpuPa3F67q9eT2vJ58p9eT4/niQLz4"
        "unFhE7/W6R6XpdfztS9x3cPevFiBd+zh4/aOFX3cfofwu7dfFuMXz9z8njvufMQ3x7eIrdmNeplwW9zMcB+8z6DgZVjCEj2m"
        "cZ7jP57akk+O7Ljchz0OxL+VaOcrjHITxuEx6NjubLllnMNZx9n8joO4vH/iHMVJiQ/wn4zePsZB2k9uUcMbsfHiZseS9ty1"
        "PV7hCPfBrx7PU58vbmsczVjDOBHfQ2y8I5bvW2vmZXiOhdV87XIav8P2fEfIVbACzRFGjOAmXqEbetz2ewvTXuLrjuG/7hMH"
        "hK9mc/u+xUYrtzjt8R1m4hjePN5rW7ctTtYa7xm3Qnb5tfMGuHBikHfYq8ceKxmvtrfYwkHny6EOx2bgO0xhym0Iexbhrp04"
        "nXO8FOeh4+vvcePCmB/DT0SZ/F1EBASRD3ZgrDERIu4kok2MXixMvFIjk9qEk39E0NmN+q2lvBSJxnti5gg7F+LOMQxGRImx"
        "5M2J5Wm0B9vhQbg28OXaYekUD85sGu5vXNk606jnq+LE2ICEd/wkIgcFdvH2EcpF6NHJ0HfN6ViL0OY5KIYiYu7kpCOGmls2"
        "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"
    ),
}


def load_list(key):
    return zlib.decompress(base64.b64decode("".join(_LISTS[key]))).decode().split()


def builtin_words():
    return load_list("words")


DANCE_SRC_W, DANCE_SRC_H, DANCE_DELAY = 240, 252, 0.1
_DANCE_SRC = (
    "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"
)

BRAILLE_BITS = ((0x01, 0x08), (0x02, 0x10), (0x04, 0x20), (0x40, 0x80))
ASCII_RAMP = " .:-=+*#%@"

MASCOT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mascots")
MASCOT_EXTS = (".gif", ".png", ".jpg", ".jpeg", ".webp")
MASCOT_SRC_W, MASCOT_SRC_H, MASCOT_MAX_FRAMES = 240, 252, 48
_MASCOT_MEM = {}
_MASCOT_ERR = {}
_MASCOT_LOCK = threading.RLock()
_ACTIVE = {"sig": None, "obj": None}
_UID = [0]


def _sat_from_rows(rows, w):
    """Summed-area table (compact int arrays) so any block can be averaged in O(1)."""
    table = bytes.maketrans(b"01", b"\x00\x01")
    sat = [array("i", [0]) * (w + 1)]
    for row in rows:
        cum = list(accumulate(row.encode("ascii").translate(table)))
        prev = sat[-1]
        sat.append(array("i", [0] + list(map(add, prev[1:], cum))))
    return sat


class Mascot:
    """A set of high-res 1-bit frames plus per-frame delays."""

    def __init__(self, key, name, w, h, frames, delays):
        _UID[0] += 1
        self.uid = _UID[0]
        self.key, self.name, self.w, self.h = key, name, w, h
        self.delays = [max(0.02, d) for d in delays]
        self.total = sum(self.delays)
        self.sats = [_sat_from_rows(rows, w) for rows in frames]

    def frame_at(self, t):
        if len(self.sats) == 1:
            return 0
        pos = t % self.total
        for i, d in enumerate(self.delays):
            if pos < d:
                return i
            pos -= d
        return len(self.sats) - 1

    def period(self):
        """How often the screen should be refreshed for this mascot."""
        return min(0.1, max(0.05, min(self.delays)))


def builtin_mascot():
    with _MASCOT_LOCK:
        if "builtin" not in _MASCOT_MEM:
            raw = zlib.decompress(base64.b64decode("".join(_DANCE_SRC))).decode()
            frames = [f.split("\n") for f in raw.split("\f")]
            _MASCOT_MEM["builtin"] = Mascot("builtin", "Rikka Takanashi", DANCE_SRC_W, DANCE_SRC_H,
                                            frames, [DANCE_DELAY] * len(frames))
        return _MASCOT_MEM["builtin"]


def list_mascots():
    try:
        files = [f for f in os.listdir(MASCOT_DIR)
                 if f.lower().endswith(MASCOT_EXTS) and os.path.isfile(os.path.join(MASCOT_DIR, f))]
    except OSError:
        return []
    return sorted(files, key=str.lower)


def have_pillow():
    try:
        import PIL  # noqa: F401
        return True
    except ImportError:
        return False


def _convert_image(path, invert, bias):
    """GIF/PNG/JPG -> list of 1-bit frames, using the same look as the built-in mascot."""
    try:
        from PIL import Image, ImageChops, ImageFilter, ImageOps
    except ImportError:
        raise RuntimeError("Pillow is needed to convert new images (pip install pillow)")
    resample = getattr(Image, "Resampling", Image).LANCZOS
    im = Image.open(path)
    n = max(1, getattr(im, "n_frames", 1))
    w0, h0 = im.size
    scale = min(MASCOT_SRC_W / w0, MASCOT_SRC_H / h0)
    sw, sh = max(8, round(w0 * scale)), max(8, round(h0 * scale))
    radius = max(2.0, 11.0 * sw / 240.0)
    thr = int(128 + (0.02 - 0.015 * bias) * 255)  # higher bias -> lower threshold -> more dots lit
    step = max(1, math.ceil(n / MASCOT_MAX_FRAMES))
    to_chr = bytes((49 if v else 48) for v in range(256))
    frames, delays = [], []
    for start in range(0, n, step):
        delay = 0.0
        for k in range(start, min(start + step, n)):
            im.seek(k)
            delay += min(1.0, max(0.02, (im.info.get("duration") or 100) / 1000.0))
        im.seek(start)
        rgba = im.convert("RGBA")
        bg = Image.new("RGBA", rgba.size, (0, 0, 0, 255))
        bg.alpha_composite(rgba)
        g = ImageOps.autocontrast(bg.convert("L"), cutoff=1).resize((sw, sh), resample)
        diff = ImageChops.subtract(g, g.filter(ImageFilter.GaussianBlur(radius)), 1.0, 128)
        mask = diff.point(lambda v, T=thr: 255 if v > T else 0)
        if invert:
            mask = ImageOps.invert(mask)
        raw = mask.tobytes().translate(to_chr)
        frames.append([raw[y * sw:(y + 1) * sw].decode("ascii") for y in range(sh)])
        delays.append(delay)
    return sw, sh, frames, delays


def _mascot_cache_path(path, invert, bias):
    st = os.stat(path)
    sig = f"{os.path.basename(path)}|{st.st_mtime_ns}|{st.st_size}|{int(invert)}|{bias}|v1"
    return os.path.join(MASCOT_DIR, ".cache", hashlib.sha1(sig.encode()).hexdigest()[:20] + ".json")


def load_mascot(key, invert=False, bias=0):
    """Built-in mascot, or a file from the mascots folder (converted once, then cached)."""
    if key == "builtin":
        return builtin_mascot()
    sig = (key, bool(invert), int(bias))
    with _MASCOT_LOCK:
        if sig in _MASCOT_MEM:
            return _MASCOT_MEM[sig]
        path = os.path.join(MASCOT_DIR, key)
        if not os.path.isfile(path):
            raise RuntimeError(f"'{key}' is not in the mascots folder")
        cache = _mascot_cache_path(path, invert, bias)
        loaded = None
        try:
            with open(cache, encoding="utf-8") as f:
                data = json.load(f)
            raw = zlib.decompress(base64.b64decode(data["data"])).decode()
            frames = [fr.split("\n") for fr in raw.split("\f")]
            loaded = (int(data["w"]), int(data["h"]), frames, [float(x) for x in data["delays"]])
            if any(len(r) != loaded[0] for fr in frames for r in fr):
                loaded = None
        except Exception:
            loaded = None
        if loaded is None:
            loaded = _convert_image(path, bool(invert), int(bias))
            try:
                os.makedirs(os.path.dirname(cache), exist_ok=True)
                w, h, frames, delays = loaded
                blob = zlib.compress("\f".join("\n".join(fr) for fr in frames).encode(), 9)
                with open(cache, "w", encoding="utf-8") as f:
                    json.dump({"w": w, "h": h, "delays": delays, "data": base64.b64encode(blob).decode()}, f)
            except OSError:
                pass
        w, h, frames, delays = loaded
        m = Mascot(key, os.path.splitext(key)[0], w, h, frames, delays)
        customs = [k for k in _MASCOT_MEM if k != "builtin"]
        for old in customs[:-3]:      # keep memory small: at most 4 converted mascots
            del _MASCOT_MEM[old]
        _MASCOT_MEM[sig] = m
        return m


def _mascot_sig(settings):
    key = settings.get("mascot", "builtin")
    o = settings.get("mascot_opts", {}).get(key, {})
    return key, bool(o.get("invert")), int(o.get("bias", 0))


def active_mascot():
    """The mascot chosen in the settings (falls back to Rikka if it can't be loaded)."""
    sig = _mascot_sig(_LIVE["settings"])
    if _ACTIVE["sig"] != sig:
        try:
            obj = load_mascot(*sig)
            _MASCOT_ERR.pop(sig[0], None)
        except Exception as e:
            _MASCOT_ERR[sig[0]] = str(e)
            obj = builtin_mascot()
        _ACTIVE["sig"], _ACTIVE["obj"] = sig, obj
    return _ACTIVE["obj"]


def mascot_name(settings):
    key = settings.get("mascot", "builtin")
    return "Rikka Takanashi" if key == "builtin" else os.path.splitext(key)[0]


def dance_layout(cols, rows):
    """Where and how big the mascot is. None = window too small (hidden).
    It grows to fill all the free space to the right of the menu."""
    m = active_mascot()
    avail_w, avail_h = cols - DANCE_X0, rows - 2
    if avail_w < 42 or avail_h < 26:
        return None
    scale = min(avail_w * 2 / m.w, avail_h * 4 / m.h, 1.3)
    tcols, trows = int(m.w * scale) // 2, int(m.h * scale) // 4
    if tcols < 4 or trows < 4:
        return None
    return DANCE_X0 + (avail_w - tcols) // 2, 1 + (avail_h - trows) // 2, tcols, trows


def _spans(n_out, n_src):
    step = n_src / n_out
    return [(int(i * step), min(n_src, max(int(i * step) + 1, math.ceil((i + 1) * step))))
            for i in range(n_out)]


def dance_frame(m, style, tcols, trows, idx):
    """Resize frame `idx` of mascot `m` to tcols x trows characters (braille or ascii)."""
    cache = _MASCOT_MEM.setdefault("out", {})
    key = (m.uid, style, tcols, trows, idx)
    if key in cache:
        return cache[key]
    if len(cache) > 400:
        cache.clear()
    sat = m.sats[idx]
    out = []
    if style == "ascii":
        xs, ys = _spans(tcols, m.w), _spans(trows, m.h)
        for y0, y1 in ys:
            line = []
            for x0, x1 in xs:
                s = sat[y1][x1] - sat[y0][x1] - sat[y1][x0] + sat[y0][x0]
                cov = s / ((x1 - x0) * (y1 - y0))
                line.append(ASCII_RAMP[min(9, int(cov ** 0.9 * 9 + 0.5))])
            out.append("".join(line))
    else:
        xs, ys = _spans(tcols * 2, m.w), _spans(trows * 4, m.h)
        for cy in range(trows):
            line = []
            for cx in range(tcols):
                v = 0
                for dy in range(4):
                    y0, y1 = ys[cy * 4 + dy]
                    for dx in range(2):
                        x0, x1 = xs[cx * 2 + dx]
                        s = sat[y1][x1] - sat[y0][x1] - sat[y1][x0] + sat[y0][x0]
                        if s * 2 >= (x1 - x0) * (y1 - y0):
                            v |= BRAILLE_BITS[dy][dx]
                line.append(chr(0x2800 + v))
            out.append("".join(line))
    cache[key] = out
    return out


# ------------------------------------------------------------------ banner art
ART = r"""
▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄           ▄▄▄▄▄▄▄▄▄▄▄▄▄  ███    ███  ▄▄▄      ▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄▄
▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄▄▄  ███           ▄▄▄▄▄▄▄▄▄▄▄▄▄   ███  ███   ███      ███  ▄▄▄▄▄▄▄▄▄▄▄▄
                       ███  ███                     ███    ██████    ███      ███              
███          ███       ███  ███           ███       ███     ████     ███      ███  ███▄▄▄▄▄▄▄▄▄
███     ███  ███▄▄▄▄▄▄▄███  ███           ███▄▄▄▄▄▄▄███     ████     ███      ███  ███▄▄▄▄▄▄▄▄▄
███     ███  ███▄▄▄▄▄▄▄███  ███           ███▄▄▄▄▄▄▄███    ██████    ███      ███           ███
███▄▄▄▄▄▄▄█  ███       ███  ███ ▄▄▄▄▄▄▄▄  ███       ███   ███  ███   ███ ▄▄▄▄▄███  ▄▄▄▄▄▄▄▄▄███
███▄▄▄▄▄▄▄▄  ███       ███  ███ ▄▄▄▄▄▄▄▄  ███       ███  ███    ███  ███ ▄▄▄▄▄█▄▄  ▄▄▄▄▄▄▄▄▄▄▄█
""".strip("\n")
ART_LINES = ART.split("\n")
ART_W = max(len(l) for l in ART_LINES)
DANCE_X0 = ART_W + 3  # first column the animation may use (right of the 95-wide UI)

# ------------------------------------------------------------------ themes
# gradient = 8 banner row colors (256-color codes); the rest are role colors.
THEMES = {
    "Galaxy":  {"gradient": [129, 135, 141, 105, 111, 75, 81, 87],   "accent": 117, "border": 99,  "available": 46,  "taken": 244, "invalid": 221, "error": 203},
    "Nebula":  {"gradient": [54, 90, 126, 162, 198, 204, 210, 216],  "accent": 213, "border": 127, "available": 46,  "taken": 244, "invalid": 221, "error": 203},
    "Inferno": {"gradient": [124, 160, 196, 202, 208, 214, 220, 226], "accent": 214, "border": 202, "available": 46,  "taken": 244, "invalid": 228, "error": 196},
    "Ocean":   {"gradient": [21, 27, 33, 39, 45, 51, 87, 123],       "accent": 45,  "border": 31,  "available": 48,  "taken": 244, "invalid": 221, "error": 203},
    "Toxic":   {"gradient": [22, 28, 34, 40, 46, 82, 118, 154],      "accent": 118, "border": 34,  "available": 46,  "taken": 245, "invalid": 221, "error": 203},
    "Sakura":  {"gradient": [125, 161, 197, 204, 211, 218, 224, 225], "accent": 218, "border": 175, "available": 120, "taken": 244, "invalid": 221, "error": 203},
    "Sunset":  {"gradient": [57, 93, 129, 165, 201, 205, 209, 214],  "accent": 209, "border": 169, "available": 46,  "taken": 244, "invalid": 228, "error": 196},
    "Matrix":  {"gradient": [22, 22, 28, 28, 34, 34, 40, 46],        "accent": 46,  "border": 28,  "available": 231, "taken": 71,  "invalid": 178, "error": 196},
    "Ice":     {"gradient": [255, 195, 159, 123, 87, 81, 75, 69],    "accent": 159, "border": 75,  "available": 48,  "taken": 244, "invalid": 221, "error": 203},
    "Blood":   {"gradient": [52, 88, 124, 160, 196, 160, 124, 88],   "accent": 196, "border": 124, "available": 46,  "taken": 245, "invalid": 221, "error": 208},
    "Mono":    {"gradient": [240, 243, 246, 249, 252, 255, 252, 249], "accent": 255, "border": 244, "available": 255, "taken": 245, "invalid": 250, "error": 196},
    # animated themes: "anim" = wave (palette scrolls down), pulse (breathing), shimmer (light sweep)
    "Aurora":     {"gradient": [46, 48, 43, 37, 33, 63, 99, 135], "anim": "wave", "speed": 3,
                   "palette": [46, 47, 48, 43, 38, 33, 63, 99, 135, 99, 63, 33, 38, 43, 48, 47],
                   "accent": 50, "border": 37, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Rainbow":    {"gradient": [196, 208, 226, 46, 51, 21, 93, 201], "anim": "wave", "speed": 5,
                   "palette": [196, 202, 208, 214, 220, 226, 190, 154, 118, 82, 46, 47, 48, 49, 50, 51, 45, 39,
                               33, 27, 21, 57, 93, 129, 165, 201, 200, 199, 198, 197],
                   "accent": 213, "border": 99, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Lava":       {"gradient": [52, 88, 124, 160, 196, 202, 208, 214], "anim": "wave", "speed": 3,
                   "palette": [88, 124, 160, 196, 202, 208, 214, 220, 214, 208, 202, 196, 160, 124],
                   "accent": 208, "border": 160, "available": 46, "taken": 245, "invalid": 228, "error": 196},
    "Neon Pulse": {"gradient": [24, 31, 38, 45, 51, 87, 123, 159], "anim": "pulse",
                   "palette": [24, 31, 38, 45, 51, 87, 123, 159, 195, 159, 123, 87, 51, 45, 38, 31],
                   "accent": 51, "border": 38, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Chrome":     {"gradient": [240, 243, 246, 249, 252, 255, 252, 249], "anim": "shimmer",
                   "accent": 255, "border": 244, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Starlight":  {"gradient": [129, 135, 141, 105, 111, 75, 81, 87], "anim": "shimmer",
                   "accent": 117, "border": 99, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Vaporwave":  {"gradient": [199, 205, 171, 135, 99, 69, 45, 51], "anim": "flow", "speed": 3,
                   "palette": [199, 206, 213, 177, 141, 105, 69, 39, 45, 51, 45, 39, 69, 105, 141, 177, 213, 206],
                   "accent": 213, "border": 99, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Plasma":     {"gradient": [201, 165, 129, 93, 57, 21, 27, 33], "anim": "flow", "speed": 4,
                   "palette": [196, 202, 208, 214, 220, 226, 190, 154, 118, 82, 46, 47, 48, 49, 50, 51, 45, 39,
                               33, 27, 21, 57, 93, 129, 165, 201, 200, 199, 198, 197],
                   "accent": 177, "border": 93, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Cyber":      {"gradient": [22, 28, 34, 40, 46, 48, 50, 51], "anim": "scan", "speed": 3,
                   "accent": 51, "border": 37, "available": 231, "taken": 245, "invalid": 221, "error": 203},
    "Stardust":   {"gradient": [54, 55, 61, 67, 73, 109, 145, 181], "anim": "sparkle", "speed": 3,
                   "accent": 183, "border": 61, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    # hidden: unlocked with a secret code in the main menu
    "Neuheit":    {"gradient": [53, 89, 125, 161, 197, 203, 209, 215], "anim": "flow", "speed": 4, "hidden": True,
                   "palette": [220, 214, 208, 202, 197, 161, 125, 89, 125, 161, 197, 202, 208, 214],
                   "accent": 220, "border": 125, "available": 46, "taken": 245, "invalid": 221, "error": 203},
    "Party":      {"gradient": [196, 208, 226, 46, 51, 21, 93, 201], "anim": "flow", "speed": 6, "hidden": True,
                   "palette": [196, 202, 208, 214, 220, 226, 190, 154, 118, 82, 46, 47, 48, 49, 50, 51, 45, 39,
                               33, 27, 21, 57, 93, 129, 165, 201, 200, 199, 198, 197],
                   "accent": 213, "border": 201, "available": 46, "taken": 245, "invalid": 221, "error": 203},
}
ROLES = ["accent", "border", "available", "taken", "invalid", "error", "banner", "dancer"]
ROLE_LABELS = {
    "accent": "Accent color",
    "border": "Box borders",
    "available": "Available names",
    "taken": "Taken names",
    "invalid": "Invalid names",
    "error": "Errors / rate limits",
    "banner": "Banner color",
    "dancer": "Mascot color",
}
NAMED = {
    "black": 232, "white": 255, "gray": 244, "grey": 244, "red": 196, "orange": 208,
    "gold": 220, "yellow": 226, "lime": 118, "green": 46, "teal": 37, "cyan": 51,
    "blue": 33, "violet": 93, "purple": 129, "magenta": 201, "pink": 213,
}

DEFAULTS = {
    "delay": 1.0,
    "prefilter": False,
    "output": "available.txt",
    "theme": "Galaxy",
    "overrides": {},
    "show_taken": True,
    "sound": "off",
    "sound_file": None,
    "sound_last": "ping",
    "shuffle": False,
    "dancer": True,
    "dancer_style": "braille",
    "skip_checked": True,
    "adaptive": True,
    "animate": True,
    "anim_style": "theme",
    "anim_speed": "normal",
    "dancer_fx": "theme",
    "mascot": "builtin",
    "mascot_opts": {},
    "unlocked": [],
}

THEME = {}
USE_COLOR = True


ANIM_STYLES = ["wave", "pulse", "shimmer", "flow", "scan", "sparkle"]
ANIM_CHOICES = ["theme", "off"] + ANIM_STYLES
ANIM_LABELS = {"theme": "Theme default", "off": "Off", "wave": "Wave", "pulse": "Pulse",
               "shimmer": "Shimmer", "flow": "Flow", "scan": "Scan", "sparkle": "Sparkle"}
SPEEDS = {"slow": 0.5, "normal": 1.0, "fast": 2.0}
SPINNER = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"


def apply_theme(settings):
    global THEME
    t = copy.deepcopy(THEMES.get(settings["theme"], THEMES["Galaxy"]))
    t["banner"] = None
    t["dancer"] = None
    t.update(settings.get("overrides", {}))
    grad = t["gradient"]
    if not t.get("palette"):
        t["palette"] = grad + grad[-2:0:-1]  # mirrored so it loops without a seam
    on = settings.get("animate", True)
    style = settings.get("anim_style", "theme")
    if not on or style == "off":
        t["anim"] = None
    elif style in ANIM_STYLES:
        t["anim"] = style
    fx = settings.get("dancer_fx", "theme")
    if not on or fx == "off":
        t["dancer_fx"] = None
    elif fx == "theme":
        t["dancer_fx"] = t.get("anim")
    else:
        t["dancer_fx"] = fx
    t["speed_mul"] = (t.get("speed", 3) / 3.0) * SPEEDS.get(settings.get("anim_speed", "normal"), 1.0)
    THEME = t


def enable_color():
    global USE_COLOR
    if os.environ.get("NO_COLOR") or not sys.stdout.isatty():
        USE_COLOR = False
    if os.name == "nt":
        os.system("")  # enable ANSI escape processing on Windows 10+


def fg(n, text, bold=False):
    if not USE_COLOR or n is None:
        return text
    return f"\033[{'1;' if bold else ''}38;5;{n}m{text}\033[0m"


def col(role, text, bold=False):
    if role == "text":
        return text
    n = 244 if role == "dim" else THEME.get(role, 255)
    return fg(n, text, bold)


def banner_color(i):
    solid = THEME.get("banner")
    return solid if solid is not None else THEME["gradient"][i % len(THEME["gradient"])]


def render(segs, width, pad=False):
    """Join colored segments, cutting at `width` visible characters."""
    out, used = [], 0
    for seg in segs:
        text, role = seg[0], seg[1]
        bold = seg[2] if len(seg) > 2 else False
        if used >= width:
            break
        text = text[: width - used]
        used += len(text)
        out.append(col(role, text, bold))
    if pad and used < width:
        out.append(" " * (width - used))
    return "".join(out)


# ------------------------------------------------------------------ color parsing
def rgb_to_256(r, g, b):
    if abs(r - g) < 8 and abs(g - b) < 8:
        v = r
        if v < 8:
            return 16
        if v > 248:
            return 231
        return min(255, 232 + round((v - 8) / 247 * 24))
    return 16 + 36 * round(r / 255 * 5) + 6 * round(g / 255 * 5) + round(b / 255 * 5)


def parse_color(s):
    s = s.strip().lower()
    if s in NAMED:
        return NAMED[s]
    if s.startswith("#") and len(s) == 7:
        try:
            return rgb_to_256(int(s[1:3], 16), int(s[3:5], 16), int(s[5:7], 16))
        except ValueError:
            return None
    if s.isdigit() and 0 <= int(s) <= 255:
        return int(s)
    return None


# ------------------------------------------------------------------ settings file
def load_settings():
    s = copy.deepcopy(DEFAULTS)
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            d = json.load(f)
        if isinstance(d.get("delay"), (int, float)) and d["delay"] >= 0:
            s["delay"] = float(d["delay"])
        for k in ("prefilter", "show_taken", "shuffle", "dancer", "skip_checked", "adaptive", "animate"):
            if isinstance(d.get(k), bool):
                s[k] = d[k]
        if isinstance(d.get("sound"), str) and (d["sound"] in SOUND_IDS or d["sound"] == "custom"):
            s["sound"] = d["sound"]
        elif d.get("beep") is True:  # older versions
            s["sound"] = "terminal"
        if (d.get("sound_last") in SOUND_IDS and d["sound_last"] != "off") or d.get("sound_last") == "custom":
            s["sound_last"] = d["sound_last"]
        if isinstance(d.get("sound_file"), str):
            s["sound_file"] = d["sound_file"]
        if d.get("anim_style") in ANIM_CHOICES:
            s["anim_style"] = d["anim_style"]
        if d.get("anim_speed") in SPEEDS:
            s["anim_speed"] = d["anim_speed"]
        if d.get("dancer_fx") in ANIM_CHOICES:
            s["dancer_fx"] = d["dancer_fx"]
        if isinstance(d.get("mascot"), str) and d["mascot"]:
            s["mascot"] = d["mascot"]
        if isinstance(d.get("mascot_opts"), dict):
            for k, v in d["mascot_opts"].items():
                if isinstance(k, str) and isinstance(v, dict):
                    bias = v.get("bias", 0)
                    s["mascot_opts"][k] = {"invert": bool(v.get("invert", False)),
                                           "bias": max(-3, min(3, bias)) if isinstance(bias, int) else 0}
        if isinstance(d.get("unlocked"), list):
            s["unlocked"] = [x for x in d["unlocked"] if isinstance(x, str) and THEMES.get(x, {}).get("hidden")]
        if d.get("dancer_style") in ("braille", "ascii"):
            s["dancer_style"] = d["dancer_style"]
        if d.get("output") is None or isinstance(d.get("output"), str):
            s["output"] = d.get("output") or None
        if d.get("theme") in THEMES:
            s["theme"] = d["theme"]
        if isinstance(d.get("overrides"), dict):
            s["overrides"] = {k: v for k, v in d["overrides"].items()
                              if k in ROLES and isinstance(v, int) and 0 <= v <= 255}
    except (OSError, ValueError):
        pass
    return s


def save_settings(s):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(s, f, indent=2)
    except OSError:
        pass


# ------------------------------------------------------------------ banner
_SCREEN = []      # everything printed since the last clear(), so a resize can repaint it
_PENDING = [""]   # prompt text currently waiting for input
_BANNER = object()


class Dyn:
    """A line whose text is recomputed whenever the screen is repainted."""
    def __init__(self, fn):
        self.fn = fn


def print(*args, **kw):
    if kw.get("file") is None:
        _SCREEN.append(kw.get("sep", " ").join(str(a) for a in args) + kw.get("end", "\n"))
        if len(_SCREEN) > 3000:
            del _SCREEN[:1500]
    builtins.print(*args, **kw)


def input(prompt_text=""):
    _PENDING[0] = prompt_text
    try:
        answer = builtins.input(prompt_text)
    finally:
        _PENDING[0] = ""
    _SCREEN.append(prompt_text + answer + "\n")
    return answer


def print_dyn(fn):
    builtins.print(fn())
    _SCREEN.append(Dyn(fn))


def _replay_screen(cols):
    out = ["\033[2J\033[H", version_seq(*shutil.get_terminal_size((100, 30)))]
    for item in list(_SCREEN):
        if item is _BANNER:
            out.append("\n".join(banner_lines(cols)) + "\n\n")
            _LIVE["banner"] = "full" if cols - 1 >= ART_W else "title"
        elif isinstance(item, Dyn):
            out.append(item.fn() + "\n")
        else:
            out.append(item)
    out.append(_PENDING[0])
    sys.stdout.write("".join(out))
    sys.stdout.flush()


def version_seq(cols, rows):
    """Escape sequence that paints the version, dim, in the bottom-right corner."""
    if not _ALT:
        return ""
    text = f"v{VERSION}"
    return f"\0337\033[?7l\033[{rows};{max(1, cols - len(text))}H" + fg(240, text) + "\033[?7h\0338"


def clear():
    del _SCREEN[:]
    _LIVE["banner"] = None
    if sys.stdout.isatty():
        cols, rows = shutil.get_terminal_size((100, 30))
        sys.stdout.write("\033[2J\033[H" + version_seq(cols, rows))
        sys.stdout.flush()


# ------------------------------------------------------------------ sounds
SOUND_CHOICES = [
    ("off", "Off"), ("terminal", "Terminal bell"), ("ping", "Ping"), ("chime", "Chime"),
    ("coin", "Coin"), ("alert", "Alert"), ("laser", "Laser"), ("bell", "Bell"),
    ("arpeggio", "Arpeggio"),
]
SOUND_IDS = [s for s, _ in SOUND_CHOICES]
RATE = 22050


def _tone(freq, dur, kind="sine", decay=6.0, vol=0.6, sweep_to=None):
    n = int(RATE * dur)
    out, phase = [], 0.0
    for i in range(n):
        f = freq if sweep_to is None else freq + (sweep_to - freq) * (i / n)
        phase += 2 * math.pi * f / RATE
        s = math.sin(phase) if kind == "sine" else (1.0 if math.sin(phase) >= 0 else -1.0)
        env = math.exp(-decay * i / n) * min(1.0, i / (RATE * 0.005))
        out.append(s * env * vol)
    return out


def _silence(dur):
    return [0.0] * int(RATE * dur)


def _synth(name):
    if name == "ping":
        return _tone(1175, 0.35, decay=7)
    if name == "chime":
        return _tone(784, 0.28, decay=5) + _tone(1047, 0.5, decay=5)
    if name == "coin":
        return _tone(988, 0.08, "square", 1, 0.3) + _tone(1319, 0.32, "square", 5, 0.3)
    if name == "alert":
        beep = _tone(880, 0.1, "square", 0.5, 0.28) + _silence(0.07)
        return beep * 3
    if name == "laser":
        return _tone(1800, 0.3, decay=3, vol=0.5, sweep_to=250)
    if name == "bell":
        parts = [_tone(660 * m, 0.9, decay=5, vol=0.4 * a) for m, a in ((1, 1), (2.0, 0.6), (3.0, 0.4), (4.2, 0.25))]
        return [sum(v) for v in zip(*parts)]
    if name == "arpeggio":
        out = []
        for f in (523, 659, 784):
            out += _tone(f, 0.09, decay=2, vol=0.5)
        return out + _tone(1047, 0.35, decay=5, vol=0.5)
    return []


def _preset_path(name):
    folder = os.path.join(tempfile.gettempdir(), "galaxus_sounds_v1")
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, name + ".wav")
    if not os.path.isfile(path):
        samples = _synth(name)
        data = struct.pack("<%dh" % len(samples), *[max(-32767, min(32767, int(v * 32767))) for v in samples])
        with wave.open(path, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(RATE)
            w.writeframes(data)
    return path


def _play_path(path):
    if os.name == "nt":
        import winsound
        winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)
        return True
    if sys.platform == "darwin":
        cmds = [["afplay", path]]
    else:
        cmds = [["paplay", path], ["aplay", "-q", path], ["play", "-q", path],
                ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet", path],
                ["mpg123", "-q", path]]
    for cmd in cmds:
        if shutil.which(cmd[0]):
            subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return True
    return False


def play_sound(settings):
    """Play the chosen notification sound. Falls back to the terminal bell."""
    kind = settings.get("sound", "off")
    if kind == "off":
        return
    try:
        path = None
        if kind == "custom":
            path = settings.get("sound_file")
        elif kind != "terminal":
            path = _preset_path(kind)
        if path and os.path.isfile(path) and _play_path(path):
            return
    except Exception:
        pass
    sys.stdout.write("\a")
    sys.stdout.flush()


def sound_label(settings):
    kind = settings.get("sound", "off")
    if kind == "custom":
        return "Custom: " + os.path.basename(settings.get("sound_file") or "?")
    return dict(SOUND_CHOICES).get(kind, "Off")


# ------------------------------------------------------------------ dancing animation
_LIVE = {"settings": {}, "banner": None, "redraw": None, "ui": None}


def dancer_fits(cols, rows):
    """The animation only appears in a big (fullscreen-sized) window."""
    return dance_layout(cols, rows) is not None


class Dancer:
    """Background thread that (1) draws the animation in the free space on the
    right and (2) repairs the whole screen when the window is resized."""

    def __init__(self):
        self.thread = None
        self.stop_evt = threading.Event()
        self.rect = None
        self.last_size = None
        self.pending = None
        self.period = 0.1

    def start(self):
        if self.thread and self.thread.is_alive():
            return
        self.last_size = tuple(shutil.get_terminal_size((100, 30)))
        self.pending = None
        self.stop_evt.clear()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def stop(self):
        self.stop_evt.set()
        if self.thread:
            self.thread.join(timeout=1)
        self.thread = None
        self.rect = None

    def _erase(self):
        if self.rect:
            x0, y0, w, h = self.rect
            blank = " " * w
            sys.stdout.write("\0337\033[?7l" + "".join(f"\033[{y0 + i};{x0}H{blank}" for i in range(h))
                             + "\033[?7h\0338")
            sys.stdout.flush()
            self.rect = None

    def _run(self):
        i = 0
        while not self.stop_evt.is_set():
            try:
                self._tick(i)
            except Exception:
                pass
            i += 1
            self.stop_evt.wait(self.period)

    def _check_resize(self, size):
        """Once the window size has settled, wipe and redraw the current screen."""
        if size == self.last_size:
            self.pending = None
            return False
        if self.pending != size:
            self.pending = size  # still changing (user is dragging); wait a tick
            return False
        self.pending, self.last_size, self.rect = None, size, None
        redraw = _LIVE.get("redraw")
        if redraw:
            redraw()
        else:
            _replay_screen(size[0])
        return True

    def _banner_tick(self, size):
        """Repaint the banner rows with the animated theme's current colors."""
        mode = _LIVE.get("banner")
        if not (USE_COLOR and THEME.get("anim") and THEME.get("banner") is None and mode):
            return
        cols, rows = size
        if not _LIVE.get("redraw") and not _screen_fits(cols, rows):
            return  # a tall menu may have scrolled; don't paint over it
        art = banner_art_rows(title_only=(mode == "title"))
        out = ["\0337\033[?7l"] + [f"\033[{r + 1};1H" + txt for r, txt in enumerate(art)] + ["\033[?7h\0338"]
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def _spinner_tick(self):
        """Animate the little spinner at the start of the status line during a scan."""
        ui = _LIVE.get("ui")
        if not (ui and ui.live and ui.running and not ui.pause_start and ui.spin_row):
            return
        ch = SPINNER[int(time.time() * 10) % len(SPINNER)]
        sys.stdout.write(f"\0337\033[?7l\033[{ui.spin_row};1H" + col("accent", ch) + "\033[?7h\0338")
        sys.stdout.flush()

    def _tick(self, i):
        s = _LIVE["settings"]
        size = tuple(shutil.get_terminal_size((100, 30)))
        if self._check_resize(size):
            return
        self._banner_tick(size)
        self._spinner_tick()
        layout = dance_layout(*size) if s.get("dancer", True) else None
        if layout is None:
            self._erase()
            return
        x0, y0, tcols, trows = layout
        if self.rect and self.rect != layout:
            self._erase()
        m = active_mascot()
        self.period = m.period()
        frame = dance_frame(m, s.get("dancer_style", "braille"), tcols, trows, m.frame_at(time.time()))
        solid = THEME.get("dancer")
        grad, pal = THEME["gradient"], THEME["palette"]
        fxs = THEME.get("dancer_fx") if (solid is None and USE_COLOR) else None
        now, speed = time.time(), THEME.get("speed_mul", 1.0)
        out = ["\0337\033[?7l"]  # save cursor, turn off line wrapping so nothing can spill
        for r, line in enumerate(frame):
            if solid is not None:
                text = fg(solid, line)
            elif fxs:
                text = fx_line(fxs, r, line, trows, now, pal, grad, speed, len(pal), block=3, bold=False)
            else:
                text = fg(grad[min(len(grad) - 1, r * len(grad) // trows)], line)
            out.append(f"\033[{y0 + r};{x0}H" + text)
        out.append("\033[?7h\0338")
        sys.stdout.write("".join(out))
        sys.stdout.flush()
        self.rect = layout


DANCER = Dancer()


_ALT = False


def enter_alt():
    """Switch to the terminal's alternate screen: no scrollback, so nothing
    from earlier frames can be scrolled back to. Restored on exit."""
    global _ALT
    if sys.stdout.isatty() and not _ALT:
        sys.stdout.write("\033[?1049h\033[2J\033[H")
        sys.stdout.flush()
        _ALT = True
        DANCER.start()


def leave_alt():
    global _ALT
    if _ALT:
        _LIVE["banner"] = None
        DANCER.stop()
        sys.stdout.write("\033[?25h\033[?1049l")
        sys.stdout.flush()
        _ALT = False


atexit.register(leave_alt)


def _strip_ansi(s):
    return re.sub(r"\033\[[0-9;?]*[A-Za-z]", "", s)


def fx_color(style, y, x, ny, nx, now, pal, grad, speed, span):
    """Color of the cell at row y / column x for an animation style.
    ny/nx = size of the thing being painted; span = palette steps from top to bottom."""
    n = len(pal)
    t = now * speed
    yn = y * 8.0 / ny              # row on the 0..8 banner scale
    xn = x * float(ART_W) / nx     # column on the 0..ART_W banner scale
    if style == "wave":            # the palette scrolls down
        return pal[math.floor(y * span / ny - t * 3) % n]
    if style == "pulse":           # a breathing ripple
        period = 2 * (n - 1)
        k = math.floor(t * 8 - y * span / ny) % period
        return pal[k if k < n else period - k]
    base = grad[min(len(grad) - 1, int(y * len(grad) / ny))]
    if style == "flow":            # a diagonal river of color
        return pal[math.floor(xn / 8 + yn * 0.7 - t * 4) % n]
    if style == "shimmer":         # a light sweeps across
        d = abs((xn - yn * 2) - ((t * 30) % (ART_W + 60) - 30))
        return 231 if d <= 2 else (195 if d <= 5 else base)
    if style == "scan":            # a bright line sweeps down
        d = abs(yn - ((t * 6) % 16 - 4))
        return 231 if d <= 0.7 else (195 if d <= 1.6 else base)
    if style == "sparkle":         # random twinkles
        h = ((x * 73856093) ^ (y * 19349663) ^ (int(t * 6) * 83492791)) % 97
        return 231 if h == 0 else (195 if h == 1 else base)
    return base


def fx_line(style, y, line, ny, now, pal, grad, speed, span, block=1, bold=True):
    """One row of text painted with an animation style (runs of equal color are merged)."""
    nx = max(1, len(line))
    if style in ("wave", "pulse"):
        return fg(fx_color(style, y, 0, ny, nx, now, pal, grad, speed, span), line, bold)
    out, run, cur = [], [], None
    for x0 in range(0, nx, block):
        c = fx_color(style, y, x0, ny, nx, now, pal, grad, speed, span)
        if c != cur and run:
            out.append(fg(cur, "".join(run), bold))
            run = []
        cur = c
        run.append(line[x0:x0 + block])
    if run:
        out.append(fg(cur, "".join(run), bold))
    return "".join(out)


def banner_art_rows(now=None, title_only=False):
    """The colored art rows. An active animation shifts the colors with the clock."""
    now = time.time() if now is None else now
    lines = ["G A L A X U S"] if title_only else ART_LINES
    style = THEME.get("anim") if (THEME.get("banner") is None and USE_COLOR) else None
    rows = []
    for i, line in enumerate(lines):
        if style:
            rows.append(fx_line(style, i, line, len(lines), now, THEME["palette"], THEME["gradient"],
                                THEME.get("speed_mul", 1.0), 8))
        else:
            rows.append(fg(banner_color(i), line, True))
    return rows


def banner_lines(cols, compact=False):
    rule = col("border", "─" * max(10, min(ART_W, cols - 1)))
    return banner_art_rows(title_only=compact or cols - 1 < ART_W) + [rule]


def _banner_height(cols):
    return (len(ART_LINES) if cols - 1 >= ART_W else 1) + 1  # art rows + rule


def _screen_fits(cols, rows):
    """True if the current menu is shorter than the window (so nothing has scrolled)."""
    n = 1 if _PENDING[0] else 0
    for item in _SCREEN:
        if item is _BANNER:
            n += _banner_height(cols) + 1
        elif isinstance(item, Dyn):
            n += 1
        else:
            n += item.count("\n")
    return n < rows


def print_banner():
    cols = shutil.get_terminal_size((100, 30)).columns
    builtins.print("\n".join(banner_lines(cols)))
    builtins.print()
    _SCREEN.append(_BANNER)
    _LIVE["banner"] = "full" if cols - 1 >= ART_W else "title"


# ------------------------------------------------------------------ roblox api
def request_with_backoff(session, method, url, on_limit=None, max_retries=6, **kwargs):
    """Returns (response, error_text). Every HTTP 429 calls on_limit(wait_seconds)."""
    backoff = 5
    for _ in range(max_retries):
        try:
            r = session.request(method, url, timeout=15, **kwargs)
        except requests.RequestException as e:
            return None, f"network error: {e}"
        if r.status_code == 429:
            try:
                wait = int(float(r.headers.get("Retry-After", backoff)))
            except ValueError:
                wait = backoff
            wait = max(wait, 1)
            if on_limit:
                on_limit(wait)
            else:
                time.sleep(wait)
            backoff = min(backoff * 2, 60)
            continue
        return r, None
    return None, "rate limited too many times"


def batch_find_taken(session, names, delay, ui, on_limit):
    taken = set()
    chunks = [names[i:i + BATCH_SIZE] for i in range(0, len(names), BATCH_SIZE)]
    for n, chunk in enumerate(chunks, 1):
        ui.status = (f"Batch lookup {n}/{len(chunks)}...", "accent")
        ui.draw(force=True)
        r, err = request_with_backoff(
            session, "POST", BATCH_URL, on_limit=on_limit,
            json={"usernames": chunk, "excludeBannedUsers": False},
        )
        if r is None or r.status_code != 200:
            ui.log("Batch lookup failed - checking those names individually", "invalid")
            continue
        try:
            for item in r.json().get("data", []):
                taken.add(item["requestedUsername"].lower())
        except (ValueError, KeyError):
            ui.log("Unexpected batch response - skipped a chunk", "invalid")
        if n < len(chunks):
            time.sleep(delay)
    return taken


def validate_username(session, username, on_limit=None):
    params = {"username": username, "birthday": "2000-01-01", "context": "Signup"}
    r, err = request_with_backoff(session, "GET", VALIDATE_URL, on_limit=on_limit, params=params)
    if r is None:
        return "ERROR", err or "request failed"
    if r.status_code != 200:
        return "ERROR", f"HTTP {r.status_code}"
    try:
        data = r.json()
    except ValueError:
        return "ERROR", "bad JSON response"
    code, message = data.get("code"), data.get("message", "")
    if code == 0:
        return "AVAILABLE", message
    if code == 1:
        return "TAKEN", message
    return "INVALID", message or f"code {code}"


# ------------------------------------------------------------------ live dashboard
def fmt_time(sec):
    sec = int(sec)
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h}h {m:02d}m" if h else f"{m}m {s:02d}s"


class Dashboard:
    """Fixed layout: banner on top, stats, a results box that scrolls inside
    itself, and a footer. Everything is redrawn in place so the art and
    status never scroll away."""

    def __init__(self, total, output, live, show_taken):
        self.total = total
        self.output = output
        self.live = live
        self.show_taken = show_taken
        self.lines = deque(maxlen=1000)
        self.counts = {"AVAILABLE": 0, "TAKEN": 0, "INVALID": 0, "ERROR": 0}
        self.ratelimits = 0
        self.done = 0
        self.status = ("Starting...", "accent")
        self.last_hit = None
        self.footer1 = [("P pause   |   Ctrl+C stop", "dim"),
                        (f"   |   hits saved to {output}" if output else "   |   not saving hits", "dim")]
        self.paused_total = 0.0
        self.pause_start = None
        self.delay_note = None
        self.running = False
        self.spin_row = None
        self.footer2 = [("Built by ", "dim"), (".gg/neuheit", "accent", True)]
        self.start = time.time()
        self._last = 0.0
        self._size = None

    def _push(self, segs):
        self.lines.append(segs)
        if self.live:
            self.draw()
        else:
            print("".join(s[0] for s in segs))

    def log(self, text, role):
        if role == "taken" and not self.show_taken:
            return
        self._push([(text, role, role == "available")])

    def log_result(self, name, status, detail=""):
        """One result row: the name is always in the terminal's normal text color
        (so it is readable in every theme); only the marker and status are tinted."""
        role = {"AVAILABLE": "available", "TAKEN": "taken", "INVALID": "invalid", "ERROR": "error"}[status]
        if role == "taken" and not self.show_taken:
            return
        marker = {"available": "[+] ", "taken": "    ", "invalid": "[~] ", "error": "[!] "}[role]
        extra = f" - {detail}" if status in ("INVALID", "ERROR") and detail else ""
        hit = role == "available"
        self._push([(marker, role, hit), (f"{name:<22}", role if hit else "text", hit), (f" {status}{extra}", role)])

    def draw(self, force=False):
        if not self.live:
            return
        now = time.time()
        if not force and now - self._last < 0.05:
            return
        self._last = now

        cols, rows = shutil.get_terminal_size((100, 30))
        header = banner_lines(cols)
        n = rows - 1 - len(header) - 7
        if n < 4 and len(header) > 2:
            header = banner_lines(cols, compact=True)
            n = rows - 1 - len(header) - 7
        n = max(n, 3)
        w = max(min(cols - 1, ART_W), 20)
        _LIVE["banner"] = "full" if len(header) > 2 else "title"

        out = ["\033[2J\033[H" if (cols, rows) != self._size else "\033[H"]
        self._size = (cols, rows)

        def put(s=""):
            vis = len(re.sub(r"\033\[[0-9;?]*[A-Za-z]", "", s))
            out.append(s + " " * max(0, w - vis) + "\n")

        for h in header:
            put(h)

        # progress line
        pct = self.done / self.total if self.total else 1.0
        paused = self.paused_total + (now - self.pause_start if self.pause_start else 0.0)
        elapsed = now - self.start - paused
        if 0 < self.done < self.total and elapsed > 1:
            eta = fmt_time(elapsed / self.done * (self.total - self.done))
        else:
            eta = "--"
        right = f" {pct * 100:5.1f}%  {self.done}/{self.total}  ETA {eta}"
        bar_w = max(5, w - len(right) - 2)
        filled = int(bar_w * pct)
        put(col("border", "[") + col("accent", "█" * filled) + col("dim", "░" * (bar_w - filled))
            + col("border", "]") + col("dim", right[: max(0, w - bar_w - 2)]))

        # counts line
        c = self.counts
        segs = [("HITS ", "dim"), (str(c["AVAILABLE"]), "available", True),
                ("   TAKEN ", "dim"), (str(c["TAKEN"]), "taken"),
                ("   INVALID ", "dim"), (str(c["INVALID"]), "invalid"),
                ("   ERRORS ", "dim"), (str(c["ERROR"]), "error")]
        if self.ratelimits:
            segs.append((f"  ({self.ratelimits} rate limits)", "dim"))
        put(render(segs, w))

        # status line
        self.spin_row = len(header) + 3
        lead = SPINNER[int(now * 10) % len(SPINNER)] if (self.running and not self.pause_start) else "»"
        segs = [(lead + " ", "accent"), (self.status[0][:50], self.status[1])]
        if self.last_hit:
            segs += [("   last hit: ", "dim"), (self.last_hit, "available", True)]
        if self.delay_note:
            segs.append(("   " + self.delay_note, "dim"))
        put(render(segs, w))

        # results box
        iw = w - 4
        put(col("border", "┌" + "─" * (w - 2) + "┐"))
        visible = list(self.lines)[-n:]
        for i in range(n):
            if i < len(visible):
                body = render(visible[i], iw, pad=True)
            else:
                body = " " * iw
            put(col("border", "│ ") + body + col("border", " │"))
        put(col("border", "└" + "─" * (w - 2) + "┘"))

        put(render(self.footer1, w))
        put(render(self.footer2, w))
        out.append(version_seq(cols, rows))
        sys.stdout.write("".join(out))
        sys.stdout.flush()


# ------------------------------------------------------------------ history, logs, keys, patterns
HISTORY_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "galaxus_history.txt")
HITS_LOG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "galaxus_hits.log")
HISTORY_DAYS = 30


def load_history():
    """name -> (letter, timestamp) for names found taken (T) or invalid (I). Newest wins."""
    seen = {}
    try:
        with open(HISTORY_PATH, encoding="utf-8") as f:
            for line in f:
                parts = line.rstrip("\n").split("\t")
                if len(parts) == 3 and parts[1] in ("T", "I"):
                    try:
                        seen[parts[0]] = (parts[1], float(parts[2]))
                    except ValueError:
                        pass
    except OSError:
        pass
    return seen


def history_recent(history):
    cutoff = time.time() - HISTORY_DAYS * 86400
    return {n for n, (_, ts) in history.items() if ts >= cutoff}


def clear_history():
    try:
        os.remove(HISTORY_PATH)
    except OSError:
        pass


def log_hit(name):
    try:
        with open(HITS_LOG_PATH, "a", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S") + "  " + name + "\n")
    except OSError:
        pass


class KeyReader:
    """Non-blocking single-key reads during a scan (used for the P = pause key).
    Does nothing when the program isn't running in a real terminal."""

    def __init__(self):
        self.active = False
        self._fd = None
        self._old = None

    def start(self):
        if not (sys.stdin.isatty() and sys.stdout.isatty()):
            return
        try:
            if os.name != "nt":
                import termios
                import tty
                self._fd = sys.stdin.fileno()
                self._old = termios.tcgetattr(self._fd)
                tty.setcbreak(self._fd)  # no echo, no Enter needed; Ctrl+C still works
            self.active = True
        except Exception:
            self.active = False

    def stop(self):
        if not self.active:
            return
        try:
            if os.name == "nt":
                import msvcrt
                while msvcrt.kbhit():
                    msvcrt.getwch()
            else:
                import termios
                termios.tcflush(self._fd, termios.TCIFLUSH)
                termios.tcsetattr(self._fd, termios.TCSADRAIN, self._old)
        except Exception:
            pass
        self.active = False

    def poll(self):
        if not self.active:
            return None
        try:
            if os.name == "nt":
                import msvcrt
                if not msvcrt.kbhit():
                    return None
                ch = msvcrt.getwch()
                if ch in ("\x00", "\xe0"):
                    msvcrt.getwch()
                    return None
                if ch == "\x03":
                    raise KeyboardInterrupt
                return ch
            import select
            if select.select([sys.stdin], [], [], 0)[0]:
                return os.read(self._fd, 1).decode(errors="ignore")
        except KeyboardInterrupt:
            raise
        except Exception:
            return None
        return None


PATTERN_CAP = 100000


def pattern_options(pat):
    """'c?v?' -> one string of allowed characters per position (or None if invalid).
    ? any letter, # any digit, V any vowel, C any consonant, anything else literal."""
    opts = []
    for ch in pat:
        if ch == "?":
            opts.append(string.ascii_lowercase)
        elif ch == "#":
            opts.append(string.digits)
        elif ch == "V":
            opts.append("aeiou")
        elif ch == "C":
            opts.append("bcdfghjklmnpqrstvwxyz")
        elif (ch.isalnum() and ch.isascii()) or ch == "_":
            opts.append(ch.lower())
        else:
            return None
    return opts if 3 <= len(opts) <= 20 else None


def pattern_total(patterns):
    return sum(math.prod(len(o) for o in p) for p in patterns)


def expand_patterns(patterns, sample=None):
    """The names the patterns match. sample=None -> all of them (random 10,000 if there are
    more than PATTERN_CAP); sample=N -> N random distinct ones (or all if fewer match)."""
    counts = [math.prod(len(o) for o in p) for p in patterns]
    seen, out = set(), []
    if sum(counts) <= PATTERN_CAP:
        for p in patterns:
            for combo in itertools.product(*p):
                name = "".join(combo)
                if name not in seen:
                    seen.add(name)
                    out.append(name)
        if sample is not None and sample < len(out):
            out = random.sample(out, sample)
        return out
    sample = min(sample or 10000, PATTERN_CAP)
    rng, tries = random.Random(), 0
    while len(out) < sample and tries < sample * 30:
        tries += 1
        p = rng.choices(patterns, weights=counts)[0]
        name = "".join(rng.choice(o) for o in p)
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


# ------------------------------------------------------------------ scan
def dedupe(names):
    seen, out = set(), []
    for n in names:
        n = n.strip()
        if n and n.lower() not in seen:
            seen.add(n.lower())
            out.append(n)
    return out


def run_scan(names, settings, wait=False):
    names = dedupe(names)
    if settings.get("shuffle"):
        random.shuffle(names)

    skipped = 0
    if settings.get("skip_checked", True) and names:
        already = history_recent(load_history())
        kept = [n for n in names if n.lower() not in already]
        skipped, names = len(names) - len(kept), kept

    if not names:
        msg = (f"All {skipped} names were already checked before. Clear the history in Settings to re-check them."
               if skipped else "No usernames to check.")
        print(col("invalid", msg))
        if wait:
            try:
                input(col("dim", "\n  Press Enter to return..."))
            except (EOFError, KeyboardInterrupt):
                pass
        return

    base_delay, output = settings["delay"], settings["output"]
    adaptive = settings.get("adaptive", True)
    live = sys.stdout.isatty()
    own_alt = live and not _ALT
    ui = Dashboard(len(names), output, live, settings["show_taken"])
    state = {"delay": base_delay, "streak": 0, "limited": False}
    session = requests.Session()
    session.headers["User-Agent"] = "galaxus-user-sniper/" + VERSION
    out = open(output, "a", encoding="utf-8") if output else None
    try:
        hist_out = open(HISTORY_PATH, "a", encoding="utf-8")
    except OSError:
        hist_out = None
    keys = KeyReader()

    def remember(name, letter):
        if hist_out:
            hist_out.write(f"{name.lower()}\t{letter}\t{time.time():.0f}\n")
            hist_out.flush()

    def poll():
        """P (or space) pauses and resumes the scan."""
        k = keys.poll()
        if k and k.lower() in ("p", " "):
            ui.pause_start = time.time()
            prev = ui.status
            ui.status = ("PAUSED - press P to resume", "invalid")
            ui.draw(force=True)
            while True:
                time.sleep(0.05)
                k2 = keys.poll()
                if k2 and k2.lower() in ("p", " "):
                    break
            ui.paused_total += time.time() - ui.pause_start
            ui.pause_start = None
            ui.status = prev
            ui.draw(force=True)

    def nap(seconds):
        """Sleep in small slices so the pause key stays responsive."""
        end = time.time() + seconds
        while True:
            poll()
            left = end - time.time()
            if left <= 0:
                break
            time.sleep(min(0.05, left))

    def on_limit(wait_s):
        # every rate limit hit counts as an error
        ui.counts["ERROR"] += 1
        ui.ratelimits += 1
        state["limited"], state["streak"] = True, 0
        if adaptive:
            state["delay"] = min(15.0, max(state["delay"] * 1.5, base_delay + 0.5))
            ui.delay_note = f"delay {state['delay']:.1f}s (auto)"
        ui.log(f"[!] RATE LIMITED - waiting {wait_s}s", "error")
        for s in range(wait_s, 0, -1):
            ui.status = (f"Rate limited - retrying in {s}s", "error")
            ui.draw(force=True)
            nap(1)

    if own_alt:
        enter_alt()
    if live:
        sys.stdout.write("\033[2J\033[?25l")
        _LIVE["redraw"] = lambda: ui.draw(force=True)
        _LIVE["ui"] = ui
    ui.draw(force=True)

    finished = False
    keys.start()
    ui.running = True
    try:
        remaining = names
        if skipped:
            ui.log(f"Skipped {skipped} names you already checked before", "accent")
        if settings["prefilter"]:
            taken = batch_find_taken(session, names, base_delay, ui, on_limit)
            for n in taken:
                remember(n, "T")
            ui.counts["TAKEN"] += len(taken)
            ui.done += len(taken)
            remaining = [n for n in names if n.lower() not in taken]
            ui.log(f"{len(taken)} names already taken, validating {len(remaining)} more", "accent")

        for idx, name in enumerate(remaining):
            poll()
            ui.status = (f"Checking: {name}", "accent")
            ui.draw()
            state["limited"] = False
            status, detail = validate_username(session, name, on_limit)
            if not state["limited"]:
                state["streak"] += 1
                if adaptive and state["delay"] > base_delay and state["streak"] >= 25:
                    state["delay"] = max(base_delay, state["delay"] * 0.85)
                    state["streak"] = 0
                    ui.delay_note = (f"delay {state['delay']:.1f}s (auto)"
                                     if state["delay"] > base_delay + 0.01 else None)
            ui.counts[status] += 1
            ui.done += 1
            if status == "TAKEN":
                remember(name, "T")
            elif status == "INVALID":
                remember(name, "I")
            elif status == "AVAILABLE":
                ui.last_hit = name
            ui.log_result(name, status, detail)
            if status == "AVAILABLE":
                if out:
                    out.write(name + "\n")
                    out.flush()
                log_hit(name)
                play_sound(settings)
            if idx < len(remaining) - 1:
                nap(state["delay"])
        finished = True
    except KeyboardInterrupt:
        pass
    finally:
        ui.running = False
        keys.stop()
        if out:
            out.close()
        if hist_out:
            hist_out.close()

    hits = ui.counts["AVAILABLE"]
    word = "Finished" if finished else "Stopped"
    ui.status = (word, "accent" if finished else "invalid")
    if output and hits:
        msg = f"{word} - {hits} available name(s) saved to {output}"
    else:
        msg = f"{word} - no available names found"
    elapsed = max(1.0, time.time() - ui.start - ui.paused_total)
    mins = elapsed / 60
    stats = (f"{ui.done} checked | {hits} hit(s) | {hits / mins:.1f} hits/min | "
             f"{ui.done / mins:.0f} names/min | {fmt_time(elapsed)}")
    if skipped:
        stats += f" | {skipped} skipped"
    ui.footer1 = [(msg, "accent", True)]
    ui.footer2 = [(stats, "dim")]
    ui.draw(force=True)
    if live:
        sys.stdout.write("\033[?25h")
        sys.stdout.flush()
    if wait:
        try:
            input(col("dim", "Press Enter to continue..."))
        except (EOFError, KeyboardInterrupt):
            pass
    _LIVE["redraw"] = None
    _LIVE["ui"] = None
    c = ui.counts
    if own_alt:
        leave_alt()
        print(msg)
    if own_alt or not live:
        print(f"{c['AVAILABLE']} available, {c['TAKEN']} taken, {c['INVALID']} invalid, {c['ERROR']} errors")
        print(stats)


# ------------------------------------------------------------------ menus
def read_file_names(path):
    path = path.strip().strip('"').strip("'")
    try:
        with open(path, encoding="utf-8-sig") as f:
            return [l.strip() for l in f if l.strip()]
    except OSError as e:
        print(col("error", f"  Could not read file: {e}"))
        return None


def opt(n, text, extra=""):
    print("  " + col("accent", f"[{n}]", True) + "  " + text + ("  " + col("dim", extra) if extra else ""))


def prompt():
    return input(col("accent", "  > ", True)).strip()


def pause():
    try:
        input(col("dim", "\n  Press Enter to continue..."))
    except (EOFError, KeyboardInterrupt):
        pass


def credits_screen():
    clear()
    print_banner()
    w = 46
    def row(segs):
        print("  " + col("border", "│ ") + render(segs, w - 4, pad=True) + col("border", " │"))
    print("  " + col("border", "┌─ CREDITS " + "─" * (w - 12) + "┐"))
    row([])
    row([("Galaxus", "accent", True)])
    row([("Roblox username availability checker", "dim")])
    row([])
    row([("Built by  ", "dim"), (".gg/neuheit", "available", True)])
    row([])
    print("  " + col("border", "└" + "─" * (w - 2) + "┘"))
    pause()


def theme_menu(settings):
    clear()
    print_banner()
    print(col("accent", "  THEMES", True) + col("dim", "   (picking one clears custom colors;  * = animated)\n"))
    names = [n for n in THEMES if not THEMES[n].get("hidden") or n in settings.get("unlocked", [])]
    half = (len(names) + 1) // 2

    def cell(idx):
        if idx >= len(names):
            return ""
        name, th = names[idx], THEMES[names[idx]]
        sw = "".join(fg(g, "█") for g in th["gradient"])
        star = "*" if th.get("anim") else " "
        cur = col("accent", " <", True) if name == settings["theme"] else "  "
        s = f"{col('accent', f'[{idx + 1:>2}]', True)}  {sw}  {name:<11}{star}{cur}"
        return s + " " * max(0, 42 - len(_strip_ansi(s)))

    for r in range(half):
        print("  " + cell(r) + cell(r + half))
    print(f"\n  {col('dim', 'Enter a number, or press Enter to go back.')}")
    try:
        ch = prompt()
    except (EOFError, KeyboardInterrupt):
        return
    if ch.isdigit() and 1 <= int(ch) <= len(names):
        settings["theme"] = names[int(ch) - 1]
        settings["overrides"] = {}
        apply_theme(settings)
        save_settings(settings)


def custom_colors_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  CUSTOM COLORS", True) + col("dim", f"   (base theme: {settings['theme']})\n"))
        for i, role in enumerate(ROLES, 1):
            cur = THEME.get(role)
            if cur is None:
                sw, val = "".join(fg(g, "█") for g in THEME["gradient"]), "gradient"
            else:
                sw, val = fg(cur, "██"), str(cur)
            tag = col("accent", " (custom)") if role in settings["overrides"] else ""
            print(f"  {col('accent', f'[{i}]', True)}  {ROLE_LABELS[role]:<28} {sw} {col('dim', val)}{tag}")
        print(f"\n  {col('accent', '[R]', True)}  Reset all custom colors")
        print(f"  {col('accent', '[B]', True)}  Back\n")
        try:
            ch = prompt().lower()
        except (EOFError, KeyboardInterrupt):
            return
        if ch in ("b", ""):
            return
        if ch == "r":
            settings["overrides"] = {}
        elif ch.isdigit() and 1 <= int(ch) <= len(ROLES):
            role = ROLES[int(ch) - 1]
            print(col("dim", "\n  Color names: red orange gold yellow lime green teal cyan blue violet purple magenta pink white gray"))
            print(col("dim", "  Or a number 0-255, or a hex code like #ff00aa. Type 'default' to reset this one."))
            try:
                raw = input(col("accent", f"  {ROLE_LABELS[role]} > ", True)).strip()
            except (EOFError, KeyboardInterrupt):
                return
            if raw.lower() in ("default", "reset"):
                settings["overrides"].pop(role, None)
            else:
                n = parse_color(raw)
                if n is None:
                    print(col("error", "  Not a valid color."))
                    pause()
                    continue
                settings["overrides"][role] = n
        else:
            continue
        apply_theme(settings)
        save_settings(settings)


def sound_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  NOTIFICATION SOUND", True) + col("dim", "   (plays when a username is available)\n"))
        for i, (sid, label) in enumerate(SOUND_CHOICES, 1):
            mark = col("accent", "  <- current", True) if settings["sound"] == sid else ""
            print(f"  {col('accent', f'[{i:>2}]', True)}  {label}{mark}")
        custom_n = len(SOUND_CHOICES) + 1
        mark = col("accent", "  <- current", True) if settings["sound"] == "custom" else ""
        print(f"  {col('accent', f'[{custom_n:>2}]', True)}  Custom sound file{mark}")
        if settings.get("sound_file"):
            print("        " + col("dim", settings["sound_file"]))
        print(f"\n  {col('accent', '[T]', True)}  Test current sound")
        print(f"  {col('accent', '[B]', True)}  Back\n")
        try:
            ch = prompt().lower()
        except (EOFError, KeyboardInterrupt):
            return
        if ch in ("b", ""):
            return
        if ch == "t":
            play_sound(settings)
            continue
        if not ch.isdigit():
            continue
        n = int(ch)
        if 1 <= n <= len(SOUND_CHOICES):
            settings["sound"] = SOUND_CHOICES[n - 1][0]
            if settings["sound"] != "off":
                settings["sound_last"] = settings["sound"]
            save_settings(settings)
            play_sound(settings)
        elif n == custom_n:
            try:
                raw = input("\n  Path to your sound file (.wav works everywhere): ").strip().strip('"').strip("'")
            except (EOFError, KeyboardInterrupt):
                continue
            if not os.path.isfile(raw):
                print(col("error", "  File not found."))
                pause()
                continue
            settings["sound"], settings["sound_file"], settings["sound_last"] = "custom", raw, "custom"
            save_settings(settings)
            play_sound(settings)


def mascot_choose_menu(settings):
    while True:
        try:
            os.makedirs(MASCOT_DIR, exist_ok=True)
        except OSError:
            pass
        files = list_mascots()
        clear()
        print_banner()
        print(col("accent", "  CHOOSE MASCOT\n", True))
        cur = settings["mascot"]
        mark = lambda k: col("accent", "  <- current", True) if k == cur else ""
        print(f"  {col('accent', '[ 1]', True)}  Rikka Takanashi{mark('builtin')}")
        for i, f in enumerate(files, 2):
            print(f"  {col('accent', f'[{i:>2}]', True)}  {f}{mark(f)}")
        print()
        print(col("dim", f"  Put your own GIF / PNG / JPG files in:  {MASCOT_DIR}"))
        if not have_pillow():
            print(col("invalid", "  Converting new files needs Pillow:  pip install pillow"))
        if cur in _MASCOT_ERR:
            print(col("error", f"  Couldn't load '{cur}': {_MASCOT_ERR[cur]}  (showing Rikka instead)"))
        print()
        opt("R", "Rescan the folder")
        opt("B", "Back")
        print()
        try:
            ch = prompt().lower()
        except (EOFError, KeyboardInterrupt):
            return
        if ch in ("b", ""):
            return
        if ch == "r" or not ch.isdigit():
            continue
        n = int(ch)
        if n == 1:
            settings["mascot"] = "builtin"
        elif 2 <= n < 2 + len(files):
            f = files[n - 2]
            o = settings["mascot_opts"].get(f, {})
            print(col("dim", "\n  Loading... (the first time it converts the file, this can take a few seconds)"))
            try:
                load_mascot(f, o.get("invert", False), o.get("bias", 0))
            except Exception as e:
                print(col("error", f"  Couldn't load it: {e}"))
                pause()
                continue
            _MASCOT_ERR.pop(f, None)
            settings["mascot"] = f
        else:
            continue
        save_settings(settings)


def _reload_mascot(settings, key, o):
    """Re-convert after invert/threshold changes; returns False (and says why) on failure."""
    print(col("dim", "\n  Converting..."))
    try:
        load_mascot(key, o["invert"], o["bias"])
    except Exception as e:
        print(col("error", f"  Couldn't convert it: {e}"))
        pause()
        return False
    return True


def dancer_menu(settings):
    while True:
        clear()
        print_banner()
        key = settings["mascot"]
        custom = key != "builtin"
        o = settings["mascot_opts"].setdefault(key, {"invert": False, "bias": 0}) if custom else {}
        need = DANCE_X0 + 42
        print(col("accent", "  MASCOT\n", True))
        opt(1, f"Show mascot: {'ON' if settings['dancer'] else 'off'}")
        opt(2, f"Mascot: {mascot_name(settings)}")
        opt(3, f"Style: {settings['dancer_style']}")
        opt(4, f"Effect: {ANIM_LABELS[settings['dancer_fx']]}")
        opt(5, "Change its color")
        if custom:
            opt(6, f"Invert (swap light and dark): {ONOFF(o['invert'])}")
            opt(7, f"Detail threshold: {o['bias']:+d}")
            back = "8"
        else:
            back = "6"
        opt(back, "Back")
        print()
        print(col("dim", f"  It only shows in a big window (at least {need} columns x 28 rows, which is "
                         f"fullscreen on most screens)"))
        print(col("dim", "  and then grows to fill all the free space on the right."))
        if key in _MASCOT_ERR:
            print(col("error", f"  Couldn't load '{key}': {_MASCOT_ERR[key]}  (showing Rikka instead)"))

        def status():
            cols, rows = shutil.get_terminal_size((100, 30))
            shown = settings["dancer"] and dancer_fits(cols, rows)
            return (col("dim", f"  Your window is {cols} x {rows} right now: ") +
                    (col("available", "visible", True) if shown else col("dim", "hidden")))
        print_dyn(status)
        print()
        try:
            ch = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        if ch == "1":
            settings["dancer"] = not settings["dancer"]
        elif ch == "2":
            mascot_choose_menu(settings)
            continue
        elif ch == "3":
            settings["dancer_style"] = "ascii" if settings["dancer_style"] == "braille" else "braille"
        elif ch == "4":
            settings["dancer_fx"] = _cycle(ANIM_CHOICES, settings["dancer_fx"])
            apply_theme(settings)
        elif ch == "5":
            custom_colors_menu(settings)
            continue
        elif custom and ch == "6":
            new = dict(o, invert=not o["invert"])
            if _reload_mascot(settings, key, new):
                settings["mascot_opts"][key] = new
        elif custom and ch == "7":
            new = dict(o, bias=o["bias"] + 1 if o["bias"] < 3 else -3)
            if _reload_mascot(settings, key, new):
                settings["mascot_opts"][key] = new
        elif ch in (back, ""):
            return
        else:
            continue
        save_settings(settings)


def _cycle(options, current):
    i = options.index(current) if current in options else -1
    return options[(i + 1) % len(options)]


ONOFF = lambda b: col("available", "on", True) if b else col("dim", "off")


def visuals_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  VISUALS\n", True))
        opt(1, f"Theme: {settings['theme']}")
        opt(2, "Custom colors")
        opt(3, f"Animations: {ONOFF(settings['animate'])}")
        opt(4, f"Banner animation: {ANIM_LABELS[settings['anim_style']]}")
        opt(5, f"Animation speed: {settings['anim_speed']}")
        opt(6, f"{mascot_name(settings)}: {ONOFF(settings['dancer'])}")
        opt(7, f"Show taken names in results: {ONOFF(settings['show_taken'])}")
        opt(8, "Back")
        print()
        try:
            ch = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        if ch == "1":
            theme_menu(settings)
            continue
        elif ch == "2":
            custom_colors_menu(settings)
            continue
        elif ch == "3":
            settings["animate"] = not settings["animate"]
            apply_theme(settings)
        elif ch == "4":
            settings["anim_style"] = _cycle(ANIM_CHOICES, settings["anim_style"])
            apply_theme(settings)
        elif ch == "5":
            settings["anim_speed"] = _cycle(list(SPEEDS), settings["anim_speed"])
            apply_theme(settings)
        elif ch == "6":
            dancer_menu(settings)
            continue
        elif ch == "7":
            settings["show_taken"] = not settings["show_taken"]
        elif ch in ("8", ""):
            return
        else:
            continue
        save_settings(settings)


def scanning_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  SCANNING\n", True))
        opt(1, f"Delay between requests: {settings['delay']}s")
        opt(2, f"Adaptive delay: {ONOFF(settings['adaptive'])}")
        opt(3, f"Prefilter: {ONOFF(settings['prefilter'])}")
        opt(4, f"Shuffle username order before scanning: {ONOFF(settings['shuffle'])}")
        opt(5, f"Skip names already checked: {ONOFF(settings['skip_checked'])}")
        opt(6, f"Output file for hits: {settings['output'] or 'none'}")
        opt(7, "Back")
        print()
        try:
            ch = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        if ch == "1":
            try:
                settings["delay"] = max(0.0, float(input("  New delay in seconds: ")))
            except (ValueError, EOFError, KeyboardInterrupt):
                pass
        elif ch == "2":
            settings["adaptive"] = not settings["adaptive"]
        elif ch == "3":
            settings["prefilter"] = not settings["prefilter"]
        elif ch == "4":
            settings["shuffle"] = not settings["shuffle"]
        elif ch == "5":
            settings["skip_checked"] = not settings["skip_checked"]
        elif ch == "6":
            try:
                v = input("  Output file (blank for none): ").strip()
            except (EOFError, KeyboardInterrupt):
                continue
            settings["output"] = v or None
        elif ch in ("7", ""):
            return
        else:
            continue
        save_settings(settings)


def data_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  DATA & RESET\n", True))
        opt(1, "Clear checked-names history")
        opt(2, "Reset all settings to default")
        opt(3, "Back")
        print()
        try:
            ch = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        if ch == "1":
            try:
                if input("  Delete the checked-names history? (y/n): ").strip().lower() == "y":
                    clear_history()
            except (EOFError, KeyboardInterrupt):
                pass
        elif ch == "2":
            try:
                if input("  Reset every setting to its default? (y/n): ").strip().lower() != "y":
                    continue
            except (EOFError, KeyboardInterrupt):
                continue
            settings.clear()
            settings.update(copy.deepcopy(DEFAULTS))
            apply_theme(settings)
            save_settings(settings)
        elif ch in ("3", ""):
            return


def settings_menu(settings):
    while True:
        clear()
        print_banner()
        print(col("accent", "  SETTINGS\n", True))
        opt(1, "Visuals")
        opt(2, "Scanning")
        opt(3, f"Sound: {sound_label(settings)}")
        opt(4, "Data & reset")
        opt(5, "Back")
        print()
        try:
            ch = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        if ch == "1":
            visuals_menu(settings)
        elif ch == "2":
            scanning_menu(settings)
        elif ch == "3":
            sound_menu(settings)
        elif ch == "4":
            data_menu(settings)
        elif ch in ("5", ""):
            return


LIST_INFO = [("3", "3-letter usernames"), ("4", "4-letter usernames"),
             ("5", "5-letter usernames"), ("6", "6-letter usernames")]

ONSETS = ["b", "br", "c", "cl", "cr", "d", "dr", "f", "fl", "fr", "g", "gl", "gr", "h", "j",
          "k", "kr", "l", "m", "n", "p", "pr", "r", "s", "sh", "sk", "sl", "sn", "st", "t",
          "th", "tr", "v", "w", "z"]
VOWELS = ["a", "e", "i", "o", "u", "a", "e", "i", "o", "u", "y", "ai", "ea", "oa", "ou", "oo", "ie"]
CODAS = ["", "", "", "n", "r", "l", "s", "t", "m", "k", "x", "d", "th", "nd", "rk", "st", "ng"]


def _fits(name, lo, hi):
    return lo <= len(name) <= hi


def _two_words(rng, pool, lo, hi):
    a, b = rng.choice(pool), rng.choice(pool)
    return a + b if a != b and _fits(a + b, lo, hi) else None


def _word_number(rng, pool, lo, hi):
    name = rng.choice(pool) + "".join(rng.choice("0123456789") for _ in range(rng.choice((1, 2, 3, 4))))
    return name if _fits(name, lo, hi) else None


def _made_up(rng, pool, lo, hi):
    parts = []
    syllables = rng.choice((2, 2, 3, 3, 4))
    for i in range(syllables):
        coda = rng.choice(CODAS) if i == syllables - 1 or rng.random() < 0.3 else ""
        parts.append(rng.choice(ONSETS) + rng.choice(VOWELS) + coda)
    name = "".join(parts)
    return name if _fits(name, lo, hi) else None


CONS = "bbcddfgghjkllmmnnppprrrsssttvwzx"
PATTERNS = {
    3: ["CVC", "CVC", "CVC", "VCV", "CCV", "VCC"],
    4: ["CVCV", "CVCV", "CVCC", "CCVC", "VCVC", "CVVC"],
    5: ["CVCVC", "CVCVC", "CCVCV", "CVCCV", "VCVCV"],
    6: ["CVCVCV", "CCVCVC", "CVCCVC", "CVCVCC", "VCVCVC"],
}


def _fixed(rng, length, mode):
    if mode == 1:  # pronounceable
        return "".join(rng.choice(CONS) if ch == "C" else rng.choice("aeiou")
                       for ch in rng.choice(PATTERNS[length]))
    if mode == 2:  # any letters
        return "".join(rng.choice(string.ascii_lowercase) for _ in range(length))
    name = "".join(rng.choice(string.ascii_lowercase + string.digits) for _ in range(length))
    return name if any(c.isalpha() for c in name) else None  # never all digits


def generate_fixed(length, mode, count):
    rng = random.Random()
    seen, out, tries = set(), [], 0
    while len(out) < count and tries < count * 60:
        tries += 1
        name = _fixed(rng, length, mode)
        if name and name not in seen:
            seen.add(name)
            out.append(name)
    return out


def generate_names(style, count, lo, hi):
    rng = random.Random()
    pool = builtin_words()[:1025]  # the hand-picked starter words
    fn = {1: _two_words, 2: _word_number, 3: _made_up}[style]
    seen, out, tries = set(), [], 0
    while len(out) < count and tries < count * 80:
        tries += 1
        name = fn(rng, pool, lo, hi)
        if name and name not in seen:
            seen.add(name)
            out.append(name)
    return out


def ask_int(label, default, lo, hi):
    try:
        raw = input(f"  {label} [{default}]: ").strip()
    except (EOFError, KeyboardInterrupt):
        return default
    if not raw:
        return default
    try:
        return max(lo, min(hi, int(raw)))
    except ValueError:
        return default


def lists_menu():
    clear()
    print_banner()
    print(col("accent", "  USERNAME LISTS\n", True))
    for i, (_, label) in enumerate(LIST_INFO, 1):
        opt(i, label, "(10,000 names)")
    opt(5, "Back")
    print()
    try:
        ch = prompt()
    except (EOFError, KeyboardInterrupt):
        return None
    if ch in ("1", "2", "3", "4"):
        return load_list(LIST_INFO[int(ch) - 1][0])
    return None


def generator_menu():
    clear()
    print_banner()
    print(col("accent", "  GENERATE RANDOM USERNAMES\n", True))
    opt(1, "Two English words combined", "(e.g. emberwolf)")
    opt(2, "English word + numbers", "(e.g. frost482)")
    opt(3, "Pronounceable made-up names", "(e.g. zorvik)")
    opt(4, "Random 3-letter names")
    opt(5, "Random 4-letter names")
    opt(6, "Random 5-letter names")
    opt(7, "Random 6-letter names")
    opt(8, "Back")
    print()
    try:
        ch = prompt()
    except (EOFError, KeyboardInterrupt):
        return None

    if ch in ("1", "2", "3"):
        print()
        count = ask_int("How many names", 1000, 1, 100000)
        lo = ask_int("Minimum length (3-20)", 5, 3, 20)
        hi = ask_int("Maximum length (3-20)", 12, lo, 20)
        names = generate_names(int(ch), count, lo, hi)
        if not names:
            print(col("error", "  Could not generate names with those lengths. Two-word names need at least 6 letters, so try a bigger maximum."))
            pause()
            return None
        return names

    if ch in ("4", "5", "6", "7"):
        length = int(ch) - 1
        print()
        opt(1, "Pronounceable", "(e.g. zork)")
        opt(2, "Any letters", "(e.g. xkqz)")
        opt(3, "Letters + numbers", "(e.g. k7m2)")
        print()
        try:
            mode = prompt()
        except (EOFError, KeyboardInterrupt):
            return None
        if mode not in ("1", "2", "3"):
            return None
        count = ask_int("How many names", 1000, 1, 100000)
        names = generate_fixed(length, int(mode), count)
        if len(names) < count:
            print(col("invalid", f"\n  Only {len(names)} unique names were possible for that setting."))
            pause()
        return names or None

    return None


def menu(settings):
    enter_alt()
    try:
        _menu_loop(settings)
    finally:
        leave_alt()


DELAY_STEPS = [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]


def toggle_sound(settings):
    """Quick on/off for the notification sound (remembers which sound was chosen)."""
    if settings["sound"] != "off":
        settings["sound_last"] = settings["sound"]
        settings["sound"] = "off"
    else:
        last = settings.get("sound_last", "ping")
        if last == "off" or (last == "custom" and not settings.get("sound_file")):
            last = "ping"
        settings["sound"] = last
        play_sound(settings)


def cycle_delay(settings):
    cur = settings["delay"]
    settings["delay"] = next((d for d in DELAY_STEPS if d > cur + 1e-9), DELAY_STEPS[0])


def quick_row(key, label, value):
    print(f"  {col('accent', f'[{key}]', True)}  {label:<26}{value}")


def pattern_menu():
    clear()
    print_banner()
    print(col("accent", "  PATTERN TEMPLATE\n", True))
    print(col("dim", "  ?  any letter          #  any digit"))
    print(col("dim", "  V  any vowel           C  any consonant"))
    print(col("dim", "  anything else is used as typed (letters, digits, _)"))
    print(col("dim", "  a pattern without ? # V or C is just one single name\n"))
    print(col("dim", "  Examples:   ??ko    c?v?    xV#?    CVCVC"))
    print(col("dim", "  Separate several patterns with spaces.\n"))
    try:
        raw = input(col("accent", "  Pattern(s) > ", True)).strip()
    except (EOFError, KeyboardInterrupt):
        return None
    if not raw:
        return None
    patterns = []
    for token in raw.replace(",", " ").split():
        opts = pattern_options(token)
        if opts is None:
            print(col("error", f"\n  Can't use '{token}': 3 to 20 characters, using only letters, digits, _, ?, #, V and C."))
            pause()
            return None
        patterns.append(opts)
    total = pattern_total(patterns)
    print(col("dim", f"\n  That matches {total:,} name{'s' if total != 1 else ''}."))
    if total == 1:
        print(col("invalid", "  Add ? # V or C to the pattern to match more than one."))
        pause()
        return expand_patterns(patterns)
    default = total if total <= PATTERN_CAP else 10000
    count = ask_int("How many names to generate", default, 1, min(total, PATTERN_CAP))
    return expand_patterns(patterns, count) or None


def start_menu(settings):
    """Everything to do with picking usernames. Returns a list of names, or None."""
    while True:
        clear()
        print_banner()
        opt(1, "Built-in word list", "(10,000 words)")
        opt(2, "3 / 4 / 5 / 6 letter username lists", "(10,000 each)")
        opt(3, "Pattern template", "(e.g. c?v? or ??ko)")
        opt(4, "Generate random usernames")
        opt(5, "Your own word list (.txt file)")
        opt(6, "Type usernames manually")
        opt(7, "Back")
        print()
        try:
            choice = prompt()
        except (EOFError, KeyboardInterrupt):
            return None
        names = None
        if choice == "1":
            names = builtin_words()
        elif choice == "2":
            names = lists_menu()
        elif choice == "3":
            names = pattern_menu()
        elif choice == "4":
            names = generator_menu()
        elif choice == "5":
            try:
                path = input("\n  Path to word list (one name per line): ")
            except (EOFError, KeyboardInterrupt):
                continue
            names = read_file_names(path)
            if names is None:
                pause()
                continue
        elif choice == "6":
            try:
                raw = input("\n  Usernames (separated by spaces or commas): ")
            except (EOFError, KeyboardInterrupt):
                continue
            names = [n for n in raw.replace(",", " ").split() if n]
        elif choice in ("7", ""):
            return None
        else:
            continue
        if names:
            return names


# ------------------------------------------------------------------ easter eggs
# Type the word at the main menu prompt -> unlocks that hidden theme (kept forever).
SECRET_THEMES = {
    "konami": "Neuheit",
    "uuddlrlrba": "Neuheit",
    "party": "Party",
}


def _unlock_theme(settings, name):
    if name in settings["unlocked"]:
        return col("dim", f"Already unlocked. The {name} theme is in Settings > Visuals > Theme.")
    settings["unlocked"].append(name)
    settings["theme"], settings["overrides"] = name, {}
    apply_theme(settings)
    save_settings(settings)
    return col("accent", f"* Secret unlocked: the {name} theme. It's yours now.", True)


def _menu_loop(settings):
    on = lambda b: col("available", "ON", True) if b else col("dim", "off")
    flash = None
    while True:
        clear()
        print_banner()
        opt(1, "Start")
        opt(2, "Settings")
        opt(3, "Credits")
        opt(4, "Exit")
        print()
        quick_row("S", "Shuffle names", on(settings["shuffle"]))
        if settings["sound"] != "off":
            beep = col("available", "ON", True) + col("dim", f"  ({sound_label(settings)})")
        else:
            beep = col("dim", "off")
        quick_row("B", "Beep sound", beep)
        quick_row("P", "Prefilter", on(settings["prefilter"]))
        quick_row("D", "Delay between requests", col("accent", f"{settings['delay']}s"))
        print()
        if flash:
            print("  " + flash)
            print()
            flash = None
        try:
            choice = prompt()
        except (EOFError, KeyboardInterrupt):
            return
        low = choice.lower().strip()

        if choice == "1":
            names = start_menu(settings)
            if names:
                run_scan(names, settings, wait=True)
        elif choice == "2":
            settings_menu(settings)
        elif choice == "3":
            credits_screen()
        elif choice == "4":
            return
        elif low == "s":
            settings["shuffle"] = not settings["shuffle"]
            save_settings(settings)
        elif low == "b":
            toggle_sound(settings)
            save_settings(settings)
        elif low == "p":
            settings["prefilter"] = not settings["prefilter"]
            save_settings(settings)
        elif low in SECRET_THEMES:
            flash = _unlock_theme(settings, SECRET_THEMES[low])
        elif re.fullmatch(r"d\s*(\d+(\.\d+)?)?\s*s?", low):
            rest = low[1:].strip().rstrip("s")
            try:
                settings["delay"] = max(0.0, float(rest))   # e.g. "d2.5" sets it exactly
            except ValueError:
                cycle_delay(settings)                       # plain "d" cycles through presets
            save_settings(settings)


# ------------------------------------------------------------------ main
def main():
    global USE_COLOR
    p = argparse.ArgumentParser(description="Galaxus User Sniper - Roblox username checker. Built by .gg/neuheit")
    p.add_argument("usernames", nargs="*", help="usernames to check (skips the menu)")
    p.add_argument("-f", "--file", help="word list file, one name per line (skips the menu)")
    p.add_argument("--builtin", action="store_true", help="use the built-in word list (skips the menu)")
    p.add_argument("--list", choices=["words", "3", "4", "5", "6"],
                   help="use a built-in list: words, or 3/4/5/6 letter usernames (skips the menu)")
    p.add_argument("-o", "--output", help="file to save hits to")
    p.add_argument("-d", "--delay", type=float, help="seconds between requests")
    p.add_argument("--prefilter", action="store_true", help="batch lookup first (faster, may rate limit)")
    p.add_argument("--shuffle", action="store_true", help="shuffle the username order before scanning")
    p.add_argument("--theme", help="theme name: " + ", ".join(THEMES))
    p.add_argument("--no-color", action="store_true", help="disable colors")
    p.add_argument("--no-dancer", action="store_true", help="hide the mascot")
    p.add_argument("--mascot", help="mascot file from the mascots folder (or 'builtin' for Rikka Takanashi)")
    p.add_argument("--pattern", nargs="+", help="pattern template(s) such as c?v? or ??ko (skips the menu)")
    p.add_argument("--count", type=int, help="with --pattern: how many names to generate")
    p.add_argument("--fresh", action="store_true", help="don't skip names checked in earlier runs")
    args = p.parse_args()

    enable_color()
    if args.no_color:
        USE_COLOR = False

    settings = load_settings()
    if args.theme:
        match = next((t for t in THEMES if t.lower() == args.theme.lower()), None)
        if not match:
            sys.exit("Unknown theme. Choose from: " + ", ".join(THEMES))
        settings["theme"] = match
        settings["overrides"] = {}
    if args.no_dancer:
        settings["dancer"] = False
    if args.mascot:
        settings["mascot"] = args.mascot
    apply_theme(settings)
    _LIVE["settings"] = settings

    if not (args.usernames or args.file or args.builtin or args.list or args.pattern):
        menu(settings)
        return

    names = list(args.usernames)
    if args.file:
        loaded = read_file_names(args.file)
        if loaded is None:
            sys.exit(1)
        names += loaded
    if args.builtin:
        names += builtin_words()
    if args.list:
        names += load_list(args.list)
    if args.pattern:
        pats = [pattern_options(x) for x in args.pattern]
        if any(x is None for x in pats):
            sys.exit("Bad pattern. Use 3-20 characters of letters, digits, _, ?, #, V (vowel) and C (consonant).")
        names += expand_patterns(pats, args.count)
    if args.fresh:
        settings["skip_checked"] = False
    if args.delay is not None:
        settings["delay"] = max(0.0, args.delay)
    if args.output:
        settings["output"] = args.output
    if args.prefilter:
        settings["prefilter"] = True
    if args.shuffle:
        settings["shuffle"] = True
    run_scan(names, settings, wait=sys.stdout.isatty())


if __name__ == "__main__":
    main()
