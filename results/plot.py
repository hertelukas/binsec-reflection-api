#!/usr/bin/env python3

import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import matplotlib.patches as patches


def plot_time(data):
    plt.figure()
    g = sns.FacetGrid(data, col="Tool")
    g.map(sns.boxplot, "Summary", "Time (s)", order=["Concrete", "Native", "C"])

    for ax in g.axes.flat:
        ax.set_yscale("log")

    plt.savefig("time.pdf", format="pdf")


def plot_paths(data):
    plt.figure()
    g = sns.FacetGrid(data, col="Tool")
    g.map(sns.boxplot, "Summary", "Paths", order=["Concrete", "Native", "C"])

    for ax in g.axes.flat:
        ax.set_yscale("log")

    plt.savefig("paths.pdf", format="pdf")


# Calculating speedup
def plot_speedup_regression(data):
    plt.figure()
    df_c = data[data["Summary"] == "C"]
    df_concrete = data[data["Summary"] == "Concrete"]

    merged_df = pd.merge(
        df_c, df_concrete, on=["Tool", "Test"], suffixes=("_C", "_Concrete")
    )

    merged_df["Speedup"] = merged_df["Time (s)_Concrete"] / merged_df["Time (s)_C"]

    result = merged_df[["Tool", "Test", "Time (s)_C", "Time (s)_Concrete", "Speedup"]]

    sns.lmplot(
        x="Time (s)_Concrete",
        hue="Tool",
        y="Speedup",
        data=result,
        logx=True,
        height=5,
        aspect=1.5,
    )
    plt.xscale("log")
    plt.xlabel("Time (s)")
    plt.savefig("speedup_regression.pdf", format="pdf")


def plot_speedup(data, dataset="DStrings"):
    plt.figure(figsize=(10, 5))
    data = data[data["Dataset"] == dataset]
    df_c = data[data["Summary"] == "C"]
    df_concrete = data[data["Summary"] == "Concrete"]

    merged_df = pd.merge(
        df_c, df_concrete, on=["Tool", "Test"], suffixes=("_C", "_Concrete")
    )

    merged_df["Speedup"] = merged_df["Time (s)_Concrete"] / merged_df["Time (s)_C"]

    df = merged_df[["Tool", "Test", "Speedup"]]

    plot_df = df.copy()
    plot_df["Speedup"] = plot_df["Speedup"].fillna(0)
    ax = sns.barplot(x="Test", hue="Tool", y="Speedup", data=plot_df)

    for i, row in df.iterrows():
        if pd.isna(row['Speedup']):
            # Get the bar location (x position for the Test and Tool group)
            bars = ax.patches[i]
            # Add a red-striped bar at the same position with a hatch pattern
            ax.add_patch(
                patches.Rectangle(
                    (bars.get_x(), 0),    # Start position of the bar
                    bars.get_width(),     # Width of the bar
                    ax.get_ylim()[1],     # Maximum y-limit for the bar height
                    hatch='///',          # Hatch pattern for stripes
                    fill=False,           # No fill color
                    edgecolor='red',      # Red color for stripes
                    linewidth=1
                )
            )

    plt.yscale("log")
    plt.tight_layout()
    plt.savefig(f"speedup_{dataset}.pdf", format="pdf")


# Calculating path improvement
def plot_path_improvement(data, dataset="DStrings"):
    plt.figure(figsize=(10, 5))
    data = data[data["Dataset"] == dataset]
    # If time isnan, then we want to ingore a potential path
    data.loc[data["Time (s)"].isna(), "Paths"] = np.nan

    df_c = data[data["Summary"] == "C"]
    df_concrete = data[data["Summary"] == "Concrete"]

    merged_df = pd.merge(
        df_c, df_concrete, on=["Tool", "Test"], suffixes=("_C", "_Concrete")
    )

    merged_df["Path Improvement"] = merged_df["Paths_Concrete"] / merged_df["Paths_C"]

    df = merged_df[
        ["Tool", "Test", "Path Improvement"]
    ]

    plot_df = df.copy()
    # Thats a bit hacky, but we need seaborn to draw the bar, so that we can patch it
    plot_df["Path Improvement"] = plot_df["Path Improvement"].fillna(0)
    ax = sns.barplot(x="Test", hue="Tool", y="Path Improvement", data=plot_df)

    for i, row in df.iterrows():
        if pd.isna(row['Path Improvement']):
            # Get the bar location (x position for the Test and Tool group)
            bars = ax.patches[i]
            # Add a red-striped bar at the same position with a hatch pattern
            ax.add_patch(
                patches.Rectangle(
                    (bars.get_x(), 0),    # Start position of the bar
                    bars.get_width(),     # Width of the bar
                    ax.get_ylim()[1],     # Maximum y-limit for the bar height
                    hatch='///',          # Hatch pattern for stripes
                    fill=False,           # No fill color
                    edgecolor='red',      # Red color for stripes
                    linewidth=1
                )
            )

    plt.yscale("log")
    plt.tight_layout()
    plt.savefig(f"path_improvement_{dataset}.pdf", format="pdf")


if __name__ == "__main__":
    primary_color = "#002F6C"
    secondary_color = "#DC4605"
    sns.set_palette([primary_color, secondary_color])
    plt.rcParams.update({'font.size': 15})

    # Read the data
    data = pd.read_csv("results2.csv")
    # Use multi-check time for time
    data.loc[data["Tool"] == "Binsec", "Time (s)"] = data["Time (s) multi-checks"]
    data["Time (s)"] = pd.to_numeric(data["Time (s)"], errors="coerce")

    # plot_time(data)
    # plot_paths(data)
    plot_speedup(data)
    plot_speedup(data, "HashMap")
    # plot_speedup_regression(data)
    plot_path_improvement(data)
    plot_path_improvement(data, "HashMap")
