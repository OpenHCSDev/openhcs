#!/usr/bin/env bash

# Shared macOS disk-image mount lifecycle for installer builds and verification.

_openhcs_attach_disk_image() {
  local access_mode=$1
  local image_path=$2
  local mount_point=$3
  local attach_plist
  local volume_plist
  local reported_mount_point
  local owned_mount_point
  local mounted_device

  if ! attach_plist=$(/usr/bin/hdiutil attach \
    -plist \
    -nobrowse \
    "$access_mode" \
    -mountpoint "$mount_point" \
    "$image_path"); then
    return 1
  fi
  printf '%s\n' "$attach_plist" >&2
  # Attach entity order is not a topology contract. Resolve the mounted volume's
  # declared parent; checking the mount identity first prevents an ordinary
  # directory from resolving to the host filesystem after an incomplete attach.
  if ! owned_mount_point=$(cd "$mount_point" && pwd -P) || \
    ! volume_plist=$(/usr/sbin/diskutil info -plist "$owned_mount_point") || \
    ! reported_mount_point=$(printf '%s\n' "$volume_plist" | \
      /usr/bin/plutil -extract MountPoint raw -o - -) || \
    [[ "$reported_mount_point" != "$owned_mount_point" ]]; then
    printf 'Disk image did not mount at its owned path: %s.\n' "$mount_point" >&2
    return 1
  fi
  if ! mounted_device=$(printf '%s\n' "$volume_plist" | \
    /usr/bin/plutil -extract ParentWholeDisk raw -o - -) || \
    [[ ! "$mounted_device" =~ ^disk[0-9]+$ ]]; then
    printf 'Could not resolve the backing device attached from %s.\n' \
      "$image_path" >&2
    return 1
  fi
  printf '/dev/%s\n' "$mounted_device"
}

openhcs_attach_writable_disk_image() {
  _openhcs_attach_disk_image -readwrite "$1" "$2"
}

openhcs_attach_readonly_disk_image() {
  _openhcs_attach_disk_image -readonly "$1" "$2"
}

_openhcs_disk_image_holders() {
  local mounted_device=$1
  local family_plist member member_plist parent
  local index=0
  local device_paths=()

  [[ "$mounted_device" =~ ^/dev/disk[0-9]+$ ]] || return 1
  family_plist=$(/usr/sbin/diskutil list -plist "$mounted_device") || return 1
  printf '%s\n' "$family_plist" >&2
  while member=$(printf '%s\n' "$family_plist" | \
    /usr/bin/plutil -extract "AllDisks.$index" raw -o - - 2>/dev/null); do
    [[ "$member" =~ ^disk[0-9]+(s[0-9]+)*$ ]] || return 1
    member_plist=$(/usr/sbin/diskutil info -plist "/dev/$member") || return 1
    parent=$(printf '%s\n' "$member_plist" | \
      /usr/bin/plutil -extract ParentWholeDisk raw -o - -) || return 1
    if [[ "/dev/$parent" != "$mounted_device" ]]; then
      printf 'Device %s is not owned by %s; skipping holder inspection.\n' \
        "$member" "$mounted_device" >&2
      return 1
    fi
    # Disk Arbitration checks raw whole/child devices when eject is busy.
    device_paths+=("/dev/$member" "/dev/r$member")
    index=$((index + 1))
  done
  ((index > 0)) || return 1
  # Noninteractive elevation exposes root-owned handles without prompting or
  # changing anything. Failure diagnostics remain visible in the build log.
  /usr/bin/sudo -n /usr/sbin/lsof -nP -- "${device_paths[@]}" >&2
}

openhcs_detach_disk_image() {
  local mounted_device=$1

  /bin/sync
  /usr/bin/hdiutil detach "$mounted_device" || true
  if test ! -e "$mounted_device"; then
    return 0
  fi
  printf 'Releasing the still-attached owned disk image %s after normal detach.\n' \
    "$mounted_device" >&2
  /usr/sbin/diskutil info -plist "$mounted_device" >&2 || true
  _openhcs_disk_image_holders "$mounted_device" || true
  # Release filesystems separately from their backing image. Disk Arbitration
  # reports unmount dissent here; preserve it rather than retrying a busy eject.
  /usr/sbin/diskutil unmountDisk force "$mounted_device" >&2 || true
  /usr/bin/hdiutil detach -debug -force "$mounted_device" || true
  if test -e "$mounted_device"; then
    printf 'Owned disk image remains attached: %s.\n' "$mounted_device" >&2
    /usr/bin/log show --last 2m --style compact --info --debug \
      --predicate "process == 'diskarbitrationd' AND eventMessage MATCHES '.*\\\\b${mounted_device#/dev/}(s[0-9]+)*\\\\b.*'" >&2 || true
    return 1
  fi
}

openhcs_cleanup_disk_image() {
  local mounted_device=$1

  if test -e "$mounted_device"; then
    openhcs_detach_disk_image "$mounted_device" || \
      printf 'Could not clean up owned disk image %s.\n' "$mounted_device" >&2
  fi
}
