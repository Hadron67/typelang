## Syntax

## Inference rules
$$
    \frac{\Gamma \vdash a: A \otimes B}{\Gamma\vdash a: A \qquad \Gamma\vdash a: B}
$$
$$
    \frac{\Gamma\vdash a: U_\alpha \qquad \Gamma\vdash \beta < \alpha}{\Gamma\vdash a: U_\beta}
$$
$$
    \frac{\Gamma\vdash a: A \qquad \Gamma\vdash A <: B}{\Gamma\vdash a: B}
$$
$$
    \frac{\Gamma\vdash A: \mathrm{trait}(B)}{\Gamma\vdash A <: B}
$$
