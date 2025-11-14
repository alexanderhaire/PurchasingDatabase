"""
Utility script to visualize NPKACEK (Potassium Acetate 0-0-29) usage for 2023-2024.

The script plots the monthly usage provided in the user request and stores the chart
under ./reports for easy sharing in the Streamlit app or via email.
"""
from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
import pandas as pd

# Monthly usage values copied from the latest SQL extracts shared in the chat.
USAGE_DATA = {
    2023: [
        ("January", -8082.407),
        ("February", -280.36125),
        ("March", -13717.8941),
        ("April", -23079.048),
        ("May", -581.9325),
        ("June", -555.0),
        ("July", -4455.54),
        ("August", -959.8875),
        ("September", -1133.26875),
        ("October", -3948.2325),
        ("November", -384.45435),
        ("December", -1540.4766),
    ],
    2024: [
        ("January", -1892.8895),
        ("February", -364.0),
        ("March", -2113.8177),
        ("April", -2854.07625),
        ("May", -907.49608),
        ("June", -5084.46357),
        ("July", -1186.458),
        ("August", -1534.38749),
        ("September", -2863.27785),
        ("October", -1064.33759),
        ("November", -4032.51634),
        ("December", -3480.81525),
    ],
}
MONTH_ORDER = [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
]


def build_dataframe() -> pd.DataFrame:
    rows: list[dict[str, object]] = []
    for year, entries in USAGE_DATA.items():
        for month, usage in entries:
            rows.append({"Year": year, "Month": month, "Usage": usage})

    df = pd.DataFrame(rows)
    df["Month"] = pd.Categorical(df["Month"], categories=MONTH_ORDER, ordered=True)
    df.sort_values(["Month", "Year"], inplace=True)
    return df


def render_chart(df: pd.DataFrame, output_path: Path) -> None:
    pivot = df.pivot(index="Month", columns="Year", values="Usage").reindex(MONTH_ORDER)

    fig, ax = plt.subplots(figsize=(11, 5.5))
    for year in pivot.columns:
        ax.plot(pivot.index, pivot[year], marker="o", label=str(year))

    ax.axhline(0, color="black", linewidth=0.8, linestyle="--")
    ax.set_title("NPKACEK Usage (2023 vs 2024)")
    ax.set_ylabel("Usage (units, negatives = outbound)")
    ax.set_xlabel("Month")
    ax.tick_params(axis="x", rotation=45, labelsize=9)
    ax.grid(True, axis="y", linestyle=":", linewidth=0.8)
    ax.legend(title="Year", frameon=False)
    fig.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=160)
    plt.close(fig)


def main() -> None:
    df = build_dataframe()
    output_path = Path("reports") / "npkacek_usage_2023_2024.png"
    render_chart(df, output_path)

    summary = (
        df.groupby("Year")["Usage"]
        .agg(total="sum", average_monthly="mean")
        .round(2)
        .to_string()
    )
    print("Saved chart to", output_path.resolve())
    print("\nUsage summary:\n", summary)


if __name__ == "__main__":
    main()
