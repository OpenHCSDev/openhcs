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

openhcs_detach_disk_image() {
  local mounted_device=$1

  /bin/sync
  /usr/bin/hdiutil detach "$mounted_device" || true
  if test ! -e "$mounted_device"; then
    return 0
  fi
  printf 'Releasing the still-attached owned disk image %s after normal detach.\n' \
    "$mounted_device" >&2
  /usr/bin/hdiutil detach -force "$mounted_device" || true
  if test -e "$mounted_device"; then
    printf 'Owned disk image remains attached: %s.\n' "$mounted_device" >&2
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
