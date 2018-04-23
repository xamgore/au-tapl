<!-- $\texttt{tru} \equiv \Lambda \alpha.\ \lambda t^\alpha\ f^\alpha.\ t$
$\texttt{tru} \equiv \Lambda \alpha.\ \lambda t^\alpha\ f^\alpha.\ f$ -->

#### 1

> Каков тип пар ($\texttt{pair}\ \sigma\ \tau $)

$\texttt{pair} \equiv \Lambda \sigma.\ \Lambda \tau.\ \lambda x^\sigma.\ \lambda y^\tau.\ \Lambda \alpha.\ \lambda f^{\sigma \to \tau \to \alpha}.\ f\, x\, y$

$\texttt{pair}\ \sigma\ \tau\ \textcolor{red}{::}\ \sigma \to \tau \to \forall \alpha.\  (\sigma \to \tau \to \alpha) \to \alpha $


#### 2

> Реализуйте комбинаторы $\texttt{fst}$, $\texttt{snd}$ и укажите их тип.

$ \texttt{fst} \equiv \Lambda \sigma.\ \Lambda \tau.\ \lambda p^{\forall \alpha .\ (\sigma \to \tau \to \alpha) \to \alpha}.\ p\ \sigma\ (\lambda x^\sigma.\ \lambda y^\tau.\ x) $

$ \texttt{fst}\ \textcolor{red}{::}\ \forall \sigma.\ \forall \tau.\ (\forall a.\ (\sigma \to \tau \to \alpha) \to \alpha) \to \sigma $

Аналогично:


$ \texttt{snd} \equiv \Lambda \sigma.\ \Lambda \tau.\ \lambda p^{\forall \alpha .\ (\sigma \to \tau \to \alpha) \to \alpha}.\ p\ \tau\ (\lambda x^\sigma.\ \lambda y^\tau.\ y) $

$ \texttt{snd}\ \textcolor{red}{::}\ \forall \sigma.\ \forall \tau.\ (\forall a.\ (\sigma \to \tau \to \alpha) \to \alpha) \to \tau $

<!-- #### 3

> Каков тип суммы типов ($\texttt{either}\ \sigma\ \tau$)?
> Реализуйте термы, описывающие его введение и удаление. -->
