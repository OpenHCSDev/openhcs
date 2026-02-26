#!/usr/bin/env python3
"""
Generate automated plots from compiled results files based on plot_config in config.xlsx.

This script reads the plot_config sheet from config.xlsx to determine which metrics to plot,
then generates bar plots with error bars for each metric across all compiled results files.
"""

import argparse
import logging
from pathlib import Path
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib
import numpy as np
from scipy import stats

# Use non-interactive backend for multiprocessing compatibility
matplotlib.use('Agg')

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def read_plot_config(config_path: Path) -> list:
    """
    Read the plot_config sheet from config.xlsx to get list of metrics to plot.
    
    Args:
        config_path: Path to config.xlsx
        
    Returns:
        List of metric names (column names) to plot
    """
    df = pd.read_excel(config_path, sheet_name='plot_config')
    
    # Get all non-empty values from the 'Column Name' column
    metrics = df['Column Name'].dropna().tolist()
    
    logger.info(f"Found {len(metrics)} metrics to plot from config")
    for metric in metrics:
        logger.info(f"  - {metric}")
    
    return metrics


def run_statistics(data_dict: dict) -> dict:
    """
    Run statistical tests comparing conditions.

    Args:
        data_dict: Dict mapping condition names to arrays of values

    Returns:
        Dict with ANOVA p-value and pairwise comparison results
    """
    # Get all data arrays
    conditions = list(data_dict.keys())
    data_arrays = [data_dict[cond] for cond in conditions]

    # Remove empty arrays
    valid_data = [(cond, arr) for cond, arr in zip(conditions, data_arrays) if len(arr) > 0]

    if len(valid_data) < 2:
        return {'anova_p': None, 'pairwise': {}}

    conditions, data_arrays = zip(*valid_data)

    # Run one-way ANOVA
    try:
        f_stat, anova_p = stats.f_oneway(*data_arrays)
    except:
        anova_p = None

    # Run pairwise t-tests (comparing each treatment to control)
    pairwise_results = {}

    # Find control condition
    control_idx = None
    for idx, cond in enumerate(conditions):
        if 'dmso' in cond.lower() or 'control' in cond.lower():
            control_idx = idx
            break

    if control_idx is not None:
        control_data = data_arrays[control_idx]
        control_name = conditions[control_idx]

        for idx, (cond, data) in enumerate(zip(conditions, data_arrays)):
            if idx != control_idx:
                try:
                    t_stat, p_val = stats.ttest_ind(control_data, data)
                    pairwise_results[cond] = {
                        'p_value': p_val,
                        'significant': p_val < 0.05,
                        'vs_control': control_name
                    }
                except:
                    pairwise_results[cond] = {'p_value': None, 'significant': False}

    return {'anova_p': anova_p, 'pairwise': pairwise_results}


def get_significance_marker(p_value: float) -> str:
    """Get significance marker based on p-value."""
    if p_value is None:
        return ''
    elif p_value < 0.001:
        return '***'
    elif p_value < 0.01:
        return '**'
    elif p_value < 0.05:
        return '*'
    else:
        return 'ns'


def generate_plot_for_metric(
    metric_name: str,
    results_files: dict,
    output_dir: Path
) -> dict:
    """
    Generate a plot for a single metric across all results files.

    Args:
        metric_name: Name of the metric (sheet name in Excel files)
        results_files: Dict mapping file type to file path
        output_dir: Directory to save plots

    Returns:
        Dict with statistical results for this metric
    """
    logger.info(f"\n📊 Generating plots for: {metric_name}")

    # Create a figure with subplots for each file type (3 subplots in 1 row)
    fig, axes = plt.subplots(1, 3, figsize=(18, 6))
    fig.suptitle(metric_name, fontsize=16, fontweight='bold')

    file_types = [
        'normalized',
        'normalized_raw',
        'normalized_raw_per_well'
    ]

    # Better display names
    display_names = {
        'normalized': 'Normalized (Per Replicate)',
        'normalized_raw': 'Raw (Per Replicate)',
        'normalized_raw_per_well': 'Raw (Per Well)'
    }

    # Store statistics for all file types
    all_stats = {}
    
    for idx, file_type in enumerate(file_types):
        ax = axes[idx]
        file_path = results_files[file_type]
        
        try:
            # Read the specific sheet for this metric
            df = pd.read_excel(file_path, sheet_name=metric_name)
            
            # Drop the first column (Unnamed: 0 or dose index)
            df = df.iloc[:, 1:]
            
            # Get conditions (column names)
            conditions = df.columns.tolist()
            
            # For per-well files, we need to group by condition and average across wells
            if 'per_well' in file_type:
                # Group columns by condition (before the '.' separator)
                condition_groups = {}
                for col in conditions:
                    if '.' in col:
                        condition_name = col.split('.')[0]
                    else:
                        condition_name = col

                    if condition_name not in condition_groups:
                        condition_groups[condition_name] = []
                    condition_groups[condition_name].append(col)

                # Calculate mean and SEM for each condition
                means = []
                sems = []
                labels = []
                data_dict = {}
                all_values_list = []  # For scatter plot

                for condition_name, cols in condition_groups.items():
                    # Get all values across all wells for this condition
                    all_values = []
                    for col in cols:
                        # Drop NaN and filter out zeros (which represent missing/invalid data)
                        values = df[col].dropna().values
                        values = values[values != 0]  # Remove zeros
                        all_values.extend(values)

                    # Only add if we have valid data
                    if len(all_values) > 0:
                        all_values = np.array(all_values)
                        means.append(all_values.mean())
                        sems.append(all_values.std() / np.sqrt(len(all_values)))
                        label = condition_name.replace('_', ' ')
                        labels.append(label)
                        data_dict[label] = all_values
                        all_values_list.append(all_values)
                    # Don't append empty arrays - skip this condition entirely
            else:
                # For non-per-well files, use original logic
                means = []
                sems = []
                labels = []
                data_dict = {}
                all_values_list = []

                for condition in conditions:
                    # Drop NaN and filter out zeros (which represent missing/invalid data)
                    values = df[condition].dropna().values
                    values = values[values != 0]  # Remove zeros
                    # Only add if we have valid data
                    if len(values) > 0:
                        means.append(values.mean())
                        sems.append(values.std() / np.sqrt(len(values)))  # SEM
                        label = condition.replace('_', ' ')
                        labels.append(label)
                        data_dict[label] = values
                        all_values_list.append(values)
                    # Don't append empty arrays - skip this condition entirely

            # Run statistics
            stats_results = run_statistics(data_dict)
            all_stats[file_type] = stats_results

            # Create bar plot
            x_pos = np.arange(len(labels))
            bars = ax.bar(x_pos, means, yerr=sems, capsize=5, alpha=0.5, edgecolor='black', linewidth=1.5)

            # Color bars by condition
            colors = {'DMSO Control': 'gray', 'F04 Treatment': 'blue', 'FC7 Treatment': 'red'}
            for bar, label in zip(bars, labels):
                for key, color in colors.items():
                    if key.lower() in label.lower():
                        bar.set_color(color)
                        break

            # Overlay scatter points for individual data points
            for i, (x, values) in enumerate(zip(x_pos, all_values_list)):
                if len(values) > 0:
                    # Add jitter to x-coordinates for visibility
                    jitter = np.random.normal(0, 0.04, size=len(values))
                    ax.scatter(x + jitter, values, color='black', alpha=0.6, s=30, zorder=3)
            
            ax.set_xticks(x_pos)
            ax.set_xticklabels(labels, rotation=45, ha='right')
            ax.set_ylabel('Value')

            # Add title with ANOVA p-value if available
            title = display_names.get(file_type, file_type)
            if stats_results['anova_p'] is not None:
                title += f"\nANOVA p={stats_results['anova_p']:.4f}"
            ax.set_title(title, pad=20)  # Add padding to prevent overlap
            ax.grid(axis='y', alpha=0.3)

            # Add significance markers above bars
            # Calculate proper y position to avoid overlap with title
            y_max = max([m + s for m, s in zip(means, sems)]) if means else 1
            y_range = ax.get_ylim()[1] - ax.get_ylim()[0]
            y_offset = y_range * 0.03  # Smaller offset

            for i, (label, mean) in enumerate(zip(labels, means)):
                if label in stats_results['pairwise']:
                    p_val = stats_results['pairwise'][label]['p_value']
                    marker = get_significance_marker(p_val)
                    if marker:
                        # Position marker just above error bar
                        y_pos = mean + sems[i] + y_offset
                        ax.text(i, y_pos, marker,
                               ha='center', va='bottom', fontsize=10, fontweight='bold')

            # Add legend for significance markers
            if any(stats_results['pairwise'].values()):
                legend_text = '* p<0.05, ** p<0.01, *** p<0.001, ns=not significant'
                ax.text(0.5, -0.25, legend_text, transform=ax.transAxes,
                       ha='center', fontsize=8, style='italic')
            
        except Exception as e:
            logger.warning(f"  ⚠️  Could not plot {file_type}: {e}")
            ax.text(0.5, 0.5, f'No data\n{str(e)}', 
                   ha='center', va='center', transform=ax.transAxes)
            ax.set_title(file_type.replace('_', ' ').title())
    
    plt.tight_layout()
    
    # Save the plot
    safe_filename = metric_name.replace('/', '_').replace('\\', '_').replace(' ', '_')
    output_path = output_dir / f"{safe_filename}.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()

    logger.info(f"  ✓ Saved: {output_path.name}")

    return all_stats


def main():
    parser = argparse.ArgumentParser(
        description='Generate automated plots from compiled results files'
    )
    parser.add_argument(
        '--config',
        type=Path,
        required=True,
        help='Path to config.xlsx file'
    )
    parser.add_argument(
        '--results-dir',
        type=Path,
        required=True,
        help='Directory containing compiled results files'
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        help='Directory to save plots (default: results-dir/plots)'
    )
    
    args = parser.parse_args()

    # Set up output directory
    if args.output_dir is None:
        args.output_dir = args.results_dir / 'plots'

    args.output_dir.mkdir(parents=True, exist_ok=True)

    logger.info(f"\n{'='*60}")
    logger.info("Automated Plot Generation")
    logger.info(f"{'='*60}")
    logger.info(f"Config: {args.config}")
    logger.info(f"Results directory: {args.results_dir}")
    logger.info(f"Output directory: {args.output_dir}")

    # Define the 3 compiled results files (excluding normalized_per_well)
    results_files = {
        'normalized': args.results_dir / 'compiled_results_normalized.xlsx',
        'normalized_raw': args.results_dir / 'compiled_results_raw.xlsx',
        'normalized_raw_per_well': args.results_dir / 'compiled_results_raw_per_well.xlsx',
    }

    # Check that all files exist
    for file_type, file_path in results_files.items():
        if not file_path.exists():
            logger.error(f"❌ File not found: {file_path}")
            return
        logger.info(f"  ✓ Found: {file_path.name}")

    # Read plot configuration
    metrics = read_plot_config(args.config)

    if not metrics:
        logger.error("❌ No metrics found in plot_config sheet")
        return

    # Generate plots for each metric
    logger.info(f"\n{'='*60}")
    logger.info(f"Generating plots for {len(metrics)} metrics")
    logger.info(f"{'='*60}")

    # Store all statistics
    all_metrics_stats = {}

    for metric in metrics:
        try:
            stats = generate_plot_for_metric(metric, results_files, args.output_dir)
            all_metrics_stats[metric] = stats
        except Exception as e:
            logger.error(f"❌ Error plotting {metric}: {e}")
            import traceback
            traceback.print_exc()

    # Save statistics summary to CSV
    logger.info(f"\n{'='*60}")
    logger.info("Saving statistics summary")
    logger.info(f"{'='*60}")

    # Display names for cleaner output
    display_names = {
        'normalized': 'Normalized (Per Replicate)',
        'normalized_raw': 'Raw (Per Replicate)',
        'normalized_raw_per_well': 'Raw (Per Well)'
    }

    stats_rows = []
    for metric, file_stats in all_metrics_stats.items():
        for file_type, stats in file_stats.items():
            row = {
                'Metric': metric,
                'File_Type': display_names.get(file_type, file_type),
                'ANOVA_p_value': stats.get('anova_p')
            }

            # Add pairwise comparisons
            for condition, pairwise in stats.get('pairwise', {}).items():
                row[f'{condition}_p_value'] = pairwise.get('p_value')
                row[f'{condition}_significant'] = pairwise.get('significant')

            stats_rows.append(row)

    if stats_rows:
        stats_df = pd.DataFrame(stats_rows)
        stats_path = args.output_dir / 'statistics_summary.csv'
        stats_df.to_csv(stats_path, index=False)
        logger.info(f"  ✓ Saved statistics to: {stats_path.name}")

    logger.info(f"\n{'='*60}")
    logger.info(f"✅ Plot generation complete!")
    logger.info(f"Plots saved to: {args.output_dir}")
    logger.info(f"{'='*60}")


if __name__ == '__main__':
    main()

